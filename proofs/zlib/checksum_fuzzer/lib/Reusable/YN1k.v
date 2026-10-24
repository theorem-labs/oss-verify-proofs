(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YN2e YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition SCT : Z := src0_D_size_classes.
Definition ASF : Z := 384.
Definition PS_S1 : Z := src0_A_alloc_slot + 0x58.
Definition PS_S2 : Z := src0_A_alloc_slot + 0x1f0.
Definition PS_RAM : Z := src0_A_alloc_slot + 0x1f8.
Definition PS_RET : Z := src0_A_alloc_slot + 0x860.
Definition PS_JR : Z := src0_A_alloc_slot + 0x89c.
Definition regs_as : list sv :=
SLit 0 :: SOff 1 0 :: SOff 2 0 :: SOff 3 0 :: SLit TP :: map (fun r => SOff r 0) (seq 5 27).
Definition R_stackS : region := mkRegion (Some 2%nat) (-ASF) 0 (-ASF) 0 [].
Definition F_spS : afact := mkAF (CEIL_MIN + ASF) (2 ^ 63 - 1) 4.
Definition F_sc : afact := mkAF 0 47 0.
Definition F_n : afact := mkAF 0 131051 0.
Definition facts_as : facts := mkFacts [ (2%nat, F_spS); (10%nat, F_sc); (11%nat, F_n) ] [] [].
Definition mem_as : smem := [R_stackS; R_got; R_guard; R_pgsz].
Definition ss_as : sstate := mkSS src0_A_alloc_slot regs_as mem_as None facts_as.
Definition ss_a1 : sstate := Eval vm_compute in run_ ss_as.
Definition R_act : region := mkRegion (Some 33%nat) 88 96 0 0 [mkChunk 88 (CVal 8 (SOff 34 0))].
Definition F_s7 : afact := mkAF LOCK (LOCK + 376) 3.
Definition F_hd : afact := mkAF 0 (2 ^ 63) 0.
Definition station (ss : sstate) (r : reg) (v : sv) (nr : list region) (nf : list (nat * afact)) : sstate :=
mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (nr ++ ss_mem ss) None
(mkFacts (nf ++ f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Definition ss_S1 : sstate := Eval vm_compute in station ss_a1 23 (SOff 33 0) [R_act] [(33%nat, F_s7); (34%nat, F_hd)].
Definition ss_hd : sstate := Eval vm_compute in run_ ss_S1.
Definition C_hd0 : acond := mkAC BC_EQ (SOff 34 0) (SLit 0).
Definition C_hd1 : acond := mkAC BC_NE (SOff 34 0) (SLit 0).
Definition ss_t0 : sstate := Eval vm_compute in run_ (add_cond ss_hd C_hd0).
Definition R_sct : region := mkRegion (Some 36%nat) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff 35 0))].
Definition F_sct : afact := mkAF SCT (SCT + 94) 1.
Definition F_sz : afact := mkAF 1 8191 0.
Definition ss_S2 : sstate := Eval vm_compute in station ss_t0 10 (SOff 36 0) [R_sct] [(36%nat, F_sct); (35%nat, F_sz)].
Definition ss_G0r : sstate := Eval vm_compute in runto_ src0_A_alloc_meta ss_S2.
Definition ss_G0 : sstate := Eval vm_compute in
mkSS (ss_pc ss_G0r) (sr_set (sr_set (ss_regs ss_G0r) 11 (SOff 37 0)) 12 (SOff 38 0)) (ss_mem ss_G0r) (ss_resv ss_G0r) (ss_facts ss_G0r).
Definition AM_JUNK : list reg := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition R_frame : region := mkRegion (Some 2%nat) (-ASF) 0 (-ASF) 0
[mkChunk (-96) (CVal 8 (SOff 32 0)); mkChunk (-88) (CVal 8 (SOff 25 0)); mkChunk (-80) (CVal 8 (SOff 24 0));
mkChunk (-72) (CVal 8 (SOff 23 0)); mkChunk (-64) (CVal 8 (SOff 22 0)); mkChunk (-56) (CVal 8 (SOff 21 0));
mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition ss_R0 : sstate := Eval vm_compute in
junk_regs AM_JUNK 40 (mkSS PS_RAM (sr_set (ss_regs ss_G0) 10 (SLit 0)) [R_frame; R_got; R_guard] None (ss_facts ss_G0)).
Definition F_meta : afact := mkAF 4096 (CEIL_MAX - 40) 3.
Definition ss_R1 : sstate := Eval vm_compute in
junk_regs AM_JUNK 41 (mkSS PS_RAM (sr_set (ss_regs ss_G0) 10 (SOff 40 0)) [R_frame; R_got; R_guard; R_pgsz] None
(mkFacts ((40%nat, F_meta) :: f_atoms (ss_facts ss_G0)) (f_conds (ss_facts ss_G0)) (f_alias (ss_facts ss_G0)))).
Definition ss_g1 : sstate := Eval vm_compute in run_ ss_R1.
Definition ss_f0E : sstate := Eval vm_compute in run_ ss_R0.
Lemma run_as : sym_runN src0segs src0tbl FUEL ss_as = (ss_a1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit (LOCK + 88))))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_S1 : sym_runN src0segs src0tbl FUEL ss_S1 = (ss_hd, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_hd0 : sym_runN src0segs src0tbl FUEL (add_cond ss_hd C_hd0) = (ss_t0, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 1)) (SLit SCT)))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_S2 : sym_run_toN src0segs src0tbl FUEL src0_A_alloc_meta ss_S2 = (ss_G0r, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_R0 : sym_runN src0segs src0tbl FUEL ss_R0 = (ss_f0E, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_R1 : sym_runN src0segs src0tbl FUEL ss_R1 = (ss_g1, RS_stopped (SR_load (Some 33%nat) 472)).
Proof. vm_compute. reflexivity. Qed.
Lemma ss_a1_pc : ss_pc ss_a1 = PS_S1. Proof. reflexivity. Qed.
Lemma ss_t0_pc : ss_pc ss_t0 = PS_S2. Proof. reflexivity. Qed.
Lemma ss_G0_pc : ss_pc ss_G0 = src0_A_alloc_meta. Proof. reflexivity. Qed.
Definition J1LIT : Z := Eval vm_compute in (match sr_get (ss_regs ss_G0r) 11 with SLit v => v | _ => 0 end).
Lemma G0r_regs : sr_get (ss_regs ss_G0r) 11 = SLit J1LIT /\ sr_get (ss_regs ss_G0r) 12 = SOff 34 0. Proof. vm_compute. split; reflexivity. Qed.
Lemma ss_f0E_pc : ss_pc ss_f0E = PS_JR. Proof. reflexivity. Qed.
Definition regs_at (ss : sstate) (l : list reg) : list sv := map (fun r => sr_get (ss_regs ss) r) l.
Lemma G0_regs : regs_at ss_G0 [1; 2; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SLit PS_RAM; SOff 2 (-144); SLit TP; SOff 10 0; SOff 9 0; SOff 11 0; SAlu ALU_SLL (SOff 10 0) (SLit 1); SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SOff 35 0; SLit SCT; SOff 26 0; SOff 27 0].
Proof. vm_compute. reflexivity. Qed.
Lemma f0E_regs : regs_at ss_f0E [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 1 0; SOff 2 0; SOff 3 0; SLit TP; SOff 8 0; SOff 9 0; SLit (2 ^ 64 - 1); SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Proof. vm_compute. reflexivity. Qed.
Definition SCNT : Z := src0_D_small_cnt_tab.
Definition MCNT : Z := src0_D_med_cnt_tab.
Definition PS_GC : Z := src0_A_alloc_slot + 0x2c4.
Definition PS_G4 : Z := src0_A_alloc_slot + 0x2c8.
Definition gcrun_ (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL PS_GC ss).
Definition R_use : region := mkRegion (Some 33%nat) 472 480 0 0 [mkChunk 472 (CVal 8 (SOff 56 0))].
Definition F_use : afact := mkAF 0 (2 ^ 48) 0.
Definition ss_S3 : sstate := Eval vm_compute in
mkSS (ss_pc ss_g1) (ss_regs ss_g1) (R_use :: ss_mem ss_g1) None
(mkFacts ((56%nat, F_use) :: f_atoms (ss_facts ss_g1)) (f_conds (ss_facts ss_g1)) (f_alias (ss_facts ss_g1))).
Definition ss_g2 : sstate := Eval vm_compute in run_ ss_S3.
Definition C_sc8 : acond := mkAC BC_GE (SLit 8) (SOff 10 0).
Definition C_sc9 : acond := mkAC BC_LT (SLit 8) (SOff 10 0).
Lemma run_S3 : sym_runN src0segs src0tbl FUEL ss_S3 = (ss_g2, RS_stopped (SR_branch BC_LT (SLit 8) (SOff 10 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c0 : sstate := Eval vm_compute in run_ (add_cond ss_g2 C_sc8).
Lemma run_sc8 : sym_runN src0segs src0tbl FUEL (add_cond ss_g2 C_sc8) = (ss_c0, RS_stopped (SR_addr (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 3)) (SLit SCNT)))).
Proof. vm_compute. reflexivity. Qed.
Definition R_scnt : region := mkRegion (Some 57%nat) 0 3 0 0 [mkChunk 0 (CVal 1 (SOff 58 0)); mkChunk 1 (CVal 1 (SOff 59 0)); mkChunk 2 (CVal 1 (SOff 60 0))].
Definition F_scnt : afact := mkAF SCNT (SCNT + 24) 0.
Definition F_tab : afact := mkAF 4 31 0.
Definition ss_S4 : sstate := Eval vm_compute in station ss_c0 12 (SOff 57 0) [R_scnt] [(57%nat, F_scnt); (58%nat, F_tab); (59%nat, F_tab); (60%nat, F_tab)].
Definition ss_g3 : sstate := Eval vm_compute in run_ (add_cond ss_g2 C_sc9).
Lemma run_sc9 : sym_runN src0segs src0tbl FUEL (add_cond ss_g2 C_sc9) = (ss_g3, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_ADD (SLit MCNT) (SAlu ALU_AND (SOff 10 0) (SLit 3))) (SLit 0)))).
Proof. vm_compute. reflexivity. Qed.
Definition R_mcnt : region := mkRegion None MCNT (MCNT + 4) 0 0 [mkChunk MCNT (CImg 4)].
Definition ss_M (r : Z) : sstate := station ss_g3 12 (SLit (MCNT + r)) [R_mcnt] [].
Definition ss_m0_ : sstate := Eval vm_compute in gcrun_ (ss_M 0).
Lemma grun_m0_ : sym_run_toN src0segs src0tbl FUEL PS_GC (ss_M 0) = (ss_m0_, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 112))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_T : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_ (mkAC BC_GEU (SOff 56 0) (SLit 112))).
Lemma grun_m0_T : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_ (mkAC BC_GEU (SOff 56 0) (SLit 112))) = (ss_m0_T, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 28)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_TT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 28)) (SLit 20)) (SLit 0))).
Lemma grun_m0_TT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 28)) (SLit 20)) (SLit 0))) = (ss_m0_TT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_TTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))).
Lemma grun_m0_TTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))) = (ss_m0_TTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_TTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))).
Lemma grun_m0_TTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))) = (ss_m0_TTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_TTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))).
Lemma grun_m0_TTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))) = (ss_m0_TTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_TF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 28)) (SLit 20)) (SLit 0))).
Lemma grun_m0_TF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 28)) (SLit 20)) (SLit 0))) = (ss_m0_TF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_F : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_ (mkAC BC_LTU (SOff 56 0) (SLit 112))).
Lemma grun_m0_F : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_ (mkAC BC_LTU (SOff 56 0) (SLit 112))) = (ss_m0_F, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 56))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_FT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_F (mkAC BC_GEU (SOff 56 0) (SLit 56))).
Lemma grun_m0_FT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_F (mkAC BC_GEU (SOff 56 0) (SLit 56))) = (ss_m0_FT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_FTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))).
Lemma grun_m0_FTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))) = (ss_m0_FTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_FTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))).
Lemma grun_m0_FTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))) = (ss_m0_FTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_FTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))).
Lemma grun_m0_FTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 14)) (SLit 20)) (SLit 0))) = (ss_m0_FTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_FF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_F (mkAC BC_LTU (SOff 56 0) (SLit 56))).
Lemma grun_m0_FF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_F (mkAC BC_LTU (SOff 56 0) (SLit 56))) = (ss_m0_FF, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m0_FFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m0_FF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))).
Lemma grun_m0_FFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m0_FF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 7)) (SLit 20)) (SLit 0))) = (ss_m0_FFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_ : sstate := Eval vm_compute in gcrun_ (ss_M 1).
Lemma grun_m1_ : sym_run_toN src0segs src0tbl FUEL PS_GC (ss_M 1) = (ss_m1_, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 96))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_T : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_ (mkAC BC_GEU (SOff 56 0) (SLit 96))).
Lemma grun_m1_T : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_ (mkAC BC_GEU (SOff 56 0) (SLit 96))) = (ss_m1_T, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 24)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_TT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 24)) (SLit 20)) (SLit 0))).
Lemma grun_m1_TT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 24)) (SLit 20)) (SLit 0))) = (ss_m1_TT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_TTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))).
Lemma grun_m1_TTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))) = (ss_m1_TTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_TTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))).
Lemma grun_m1_TTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))) = (ss_m1_TTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_TTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))).
Lemma grun_m1_TTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))) = (ss_m1_TTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_TF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 24)) (SLit 20)) (SLit 0))).
Lemma grun_m1_TF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 24)) (SLit 20)) (SLit 0))) = (ss_m1_TF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_F : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_ (mkAC BC_LTU (SOff 56 0) (SLit 96))).
Lemma grun_m1_F : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_ (mkAC BC_LTU (SOff 56 0) (SLit 96))) = (ss_m1_F, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 48))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_F (mkAC BC_GEU (SOff 56 0) (SLit 48))).
Lemma grun_m1_FT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_F (mkAC BC_GEU (SOff 56 0) (SLit 48))) = (ss_m1_FT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))).
Lemma grun_m1_FTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))) = (ss_m1_FTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))).
Lemma grun_m1_FTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))) = (ss_m1_FTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))).
Lemma grun_m1_FTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 12)) (SLit 20)) (SLit 0))) = (ss_m1_FTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_F (mkAC BC_LTU (SOff 56 0) (SLit 48))).
Lemma grun_m1_FF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_F (mkAC BC_LTU (SOff 56 0) (SLit 48))) = (ss_m1_FF, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 24))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FFT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_FF (mkAC BC_GEU (SOff 56 0) (SLit 24))).
Lemma grun_m1_FFT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_FF (mkAC BC_GEU (SOff 56 0) (SLit 24))) = (ss_m1_FFT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FFTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_FFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))).
Lemma grun_m1_FFTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_FFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 6)) (SLit 20)) (SLit 0))) = (ss_m1_FFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_FF (mkAC BC_LTU (SOff 56 0) (SLit 24))).
Lemma grun_m1_FFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_FF (mkAC BC_LTU (SOff 56 0) (SLit 24))) = (ss_m1_FFF, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 3)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_FFFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m1_FFF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 3)) (SLit 20)) (SLit 0))).
Lemma grun_m1_FFFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m1_FFF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 3)) (SLit 20)) (SLit 0))) = (ss_m1_FFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_ : sstate := Eval vm_compute in gcrun_ (ss_M 2).
Lemma grun_m2_ : sym_run_toN src0segs src0tbl FUEL PS_GC (ss_M 2) = (ss_m2_, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 80))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_T : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_ (mkAC BC_GEU (SOff 56 0) (SLit 80))).
Lemma grun_m2_T : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_ (mkAC BC_GEU (SOff 56 0) (SLit 80))) = (ss_m2_T, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 20)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_TT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 20)) (SLit 20)) (SLit 0))).
Lemma grun_m2_TT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 20)) (SLit 20)) (SLit 0))) = (ss_m2_TT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_TTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))).
Lemma grun_m2_TTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))) = (ss_m2_TTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_TTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))).
Lemma grun_m2_TTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))) = (ss_m2_TTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_TTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))).
Lemma grun_m2_TTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))) = (ss_m2_TTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_TF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 20)) (SLit 20)) (SLit 0))).
Lemma grun_m2_TF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 20)) (SLit 20)) (SLit 0))) = (ss_m2_TF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_F : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_ (mkAC BC_LTU (SOff 56 0) (SLit 80))).
Lemma grun_m2_F : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_ (mkAC BC_LTU (SOff 56 0) (SLit 80))) = (ss_m2_F, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 40))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_FT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_F (mkAC BC_GEU (SOff 56 0) (SLit 40))).
Lemma grun_m2_FT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_F (mkAC BC_GEU (SOff 56 0) (SLit 40))) = (ss_m2_FT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_FTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))).
Lemma grun_m2_FTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))) = (ss_m2_FTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_FTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))).
Lemma grun_m2_FTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))) = (ss_m2_FTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_FTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))).
Lemma grun_m2_FTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 10)) (SLit 20)) (SLit 0))) = (ss_m2_FTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_FF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_F (mkAC BC_LTU (SOff 56 0) (SLit 40))).
Lemma grun_m2_FF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_F (mkAC BC_LTU (SOff 56 0) (SLit 40))) = (ss_m2_FF, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m2_FFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m2_FF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))).
Lemma grun_m2_FFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m2_FF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 5)) (SLit 20)) (SLit 0))) = (ss_m2_FFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_ : sstate := Eval vm_compute in gcrun_ (ss_M 3).
Lemma grun_m3_ : sym_run_toN src0segs src0tbl FUEL PS_GC (ss_M 3) = (ss_m3_, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 128))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_T : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_ (mkAC BC_GEU (SOff 56 0) (SLit 128))).
Lemma grun_m3_T : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_ (mkAC BC_GEU (SOff 56 0) (SLit 128))) = (ss_m3_T, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 32)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_TT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 32)) (SLit 20)) (SLit 0))).
Lemma grun_m3_TT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_T (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 32)) (SLit 20)) (SLit 0))) = (ss_m3_TT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_TTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))).
Lemma grun_m3_TTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_TT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))) = (ss_m3_TTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_TTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))).
Lemma grun_m3_TTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_TTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))) = (ss_m3_TTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_TTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))).
Lemma grun_m3_TTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_TT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))) = (ss_m3_TTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_TF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 32)) (SLit 20)) (SLit 0))).
Lemma grun_m3_TF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_T (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 32)) (SLit 20)) (SLit 0))) = (ss_m3_TF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_F : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_ (mkAC BC_LTU (SOff 56 0) (SLit 128))).
Lemma grun_m3_F : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_ (mkAC BC_LTU (SOff 56 0) (SLit 128))) = (ss_m3_F, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 64))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_F (mkAC BC_GEU (SOff 56 0) (SLit 64))).
Lemma grun_m3_FT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_F (mkAC BC_GEU (SOff 56 0) (SLit 64))) = (ss_m3_FT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FTT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))).
Lemma grun_m3_FTT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FT (mkAC BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))) = (ss_m3_FTT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FTTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))).
Lemma grun_m3_FTTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FTT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))) = (ss_m3_FTTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))).
Lemma grun_m3_FTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)) (SLit 20)) (SLit 0))) = (ss_m3_FTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_F (mkAC BC_LTU (SOff 56 0) (SLit 64))).
Lemma grun_m3_FF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_F (mkAC BC_LTU (SOff 56 0) (SLit 64))) = (ss_m3_FF, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 32))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FF (mkAC BC_GEU (SOff 56 0) (SLit 32))).
Lemma grun_m3_FFT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FF (mkAC BC_GEU (SOff 56 0) (SLit 32))) = (ss_m3_FFT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))).
Lemma grun_m3_FFTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 8)) (SLit 20)) (SLit 0))) = (ss_m3_FFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FF (mkAC BC_LTU (SOff 56 0) (SLit 32))).
Lemma grun_m3_FFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FF (mkAC BC_LTU (SOff 56 0) (SLit 32))) = (ss_m3_FFF, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 16))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFFT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFF (mkAC BC_GEU (SOff 56 0) (SLit 16))).
Lemma grun_m3_FFFT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFF (mkAC BC_GEU (SOff 56 0) (SLit 16))) = (ss_m3_FFFT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 4)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFFTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 4)) (SLit 20)) (SLit 0))).
Lemma grun_m3_FFFTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 4)) (SLit 20)) (SLit 0))) = (ss_m3_FFFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFF (mkAC BC_LTU (SOff 56 0) (SLit 16))).
Lemma grun_m3_FFFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFF (mkAC BC_LTU (SOff 56 0) (SLit 16))) = (ss_m3_FFFF, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SLit 8))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFFFT : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFFF (mkAC BC_GEU (SOff 56 0) (SLit 8))).
Lemma grun_m3_FFFFT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFFF (mkAC BC_GEU (SOff 56 0) (SLit 8))) = (ss_m3_FFFFT, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 2)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFFFTF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFFFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 2)) (SLit 20)) (SLit 0))).
Lemma grun_m3_FFFFTF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFFFT (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 2)) (SLit 20)) (SLit 0))) = (ss_m3_FFFFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFFFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFFF (mkAC BC_LTU (SOff 56 0) (SLit 8))).
Lemma grun_m3_FFFFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFFF (mkAC BC_LTU (SOff 56 0) (SLit 8))) = (ss_m3_FFFFF, RS_stopped (SR_branch BC_NE (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 1)) (SLit 20)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_m3_FFFFFF : sstate := Eval vm_compute in gcrun_ (add_cond ss_m3_FFFFF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 1)) (SLit 20)) (SLit 0))).
Lemma grun_m3_FFFFFF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_m3_FFFFF (mkAC BC_EQ (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 1)) (SLit 20)) (SLit 0))) = (ss_m3_FFFFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_ : sstate := Eval vm_compute in gcrun_ ss_S4.
Lemma grun_c_ : sym_run_toN src0segs src0tbl FUEL PS_GC ss_S4 = (ss_c_, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 58 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_T : sstate := Eval vm_compute in gcrun_ (add_cond ss_c_ (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 58 0) (SLit 2)))).
Lemma grun_c_T : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_c_ (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 58 0) (SLit 2)))) = (ss_c_T, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_F : sstate := Eval vm_compute in gcrun_ (add_cond ss_c_ (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 58 0) (SLit 2)))).
Lemma grun_c_F : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_c_ (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 58 0) (SLit 2)))) = (ss_c_F, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 59 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FT : sstate := Eval vm_compute in gcrun_ (add_cond ss_c_F (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 59 0) (SLit 2)))).
Lemma grun_c_FT : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_c_F (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 59 0) (SLit 2)))) = (ss_c_FT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FF : sstate := Eval vm_compute in gcrun_ (add_cond ss_c_F (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 59 0) (SLit 2)))).
Lemma grun_c_FF : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_c_F (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 59 0) (SLit 2)))) = (ss_c_FF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition GC_JUNK : list reg := [19; 14; 15]%bv.
Definition facts_GC : facts :=
mkFacts ((61%nat, mkAF 1 32 0) :: (62%nat, mkAF 16 4194304 4) :: f_atoms (ss_facts ss_S3)) (f_conds (ss_facts ss_S3)) [].
Definition ss_GC : sstate := Eval vm_compute in setfacts facts_GC (setmem (ss_mem ss_S3) (junk_regs GC_JUNK 61 ss_c_T)).
Definition gc_check (ss : sstate) : bool :=
ss_atoms_lt 61 ss && sv_eqb (sr_get (ss_regs ss) 14) (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (sr_get (ss_regs ss) 19))
&& mergeb ss_GC (setfacts facts_GC (junk_regs GC_JUNK 61 ss)).
Lemma ss_GC_pc : ss_pc ss_GC = PS_GC. Proof. reflexivity. Qed.
Lemma gc_m0_TTTF : gc_check ss_m0_TTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m0_TTF : gc_check ss_m0_TTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m0_TF : gc_check ss_m0_TF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m0_FTTF : gc_check ss_m0_FTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m0_FTF : gc_check ss_m0_FTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m0_FFF : gc_check ss_m0_FFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m1_TTTF : gc_check ss_m1_TTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m1_TTF : gc_check ss_m1_TTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m1_TF : gc_check ss_m1_TF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m1_FTTF : gc_check ss_m1_FTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m1_FTF : gc_check ss_m1_FTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m1_FFTF : gc_check ss_m1_FFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m1_FFFF : gc_check ss_m1_FFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m2_TTTF : gc_check ss_m2_TTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m2_TTF : gc_check ss_m2_TTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m2_TF : gc_check ss_m2_TF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m2_FTTF : gc_check ss_m2_FTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m2_FTF : gc_check ss_m2_FTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m2_FFF : gc_check ss_m2_FFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_TTTF : gc_check ss_m3_TTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_TTF : gc_check ss_m3_TTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_TF : gc_check ss_m3_TF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_FTTF : gc_check ss_m3_FTTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_FTF : gc_check ss_m3_FTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_FFTF : gc_check ss_m3_FFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_FFFTF : gc_check ss_m3_FFFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_FFFFTF : gc_check ss_m3_FFFFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_m3_FFFFFF : gc_check ss_m3_FFFFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_c_T : gc_check ss_c_T = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_c_FT : gc_check ss_c_FT = true. Proof. vm_compute. reflexivity. Qed.
Lemma gc_c_FF : gc_check ss_c_FF = true. Proof. vm_compute. reflexivity. Qed.
Definition ss_g4 : sstate := Eval vm_compute in run_ ss_GC.
Lemma run_GC : sym_runN src0segs src0tbl FUEL ss_GC = (ss_g4, RS_stopped (SR_branch BC_GEU (SLit 2048) (SOff 62 16))).
Proof. vm_compute. reflexivity. Qed.
Definition C_nest : acond := mkAC BC_GEU (SLit 2048) (SOff 62 16).
Definition C_mm : acond := mkAC BC_LTU (SLit 2048) (SOff 62 16).
Lemma GC_regs : regs_at ss_GC [1; 2; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 41 0; SOff 2 (-144); SLit TP; SOff 10 0; SOff 40 0; SOff 56 0; SLit 4096; SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16); SLit 2048; SOff 62 0;
SOff 11 0; SOff 61 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SAlu ALU_SLL (SOff 35 0) (SLit 4); SLit SCT; SOff 26 0; SOff 27 0].
Proof. vm_compute. reflexivity. Qed.
Lemma grun_R1 : sym_run_toN src0segs src0tbl FUEL PS_GC ss_R1 = (ss_g1, RS_stopped (SR_load (Some 33%nat) 472)).
Proof. vm_compute. reflexivity. Qed.
Lemma grun_S3 : sym_run_toN src0segs src0tbl FUEL PS_GC ss_S3 = (ss_g2, RS_stopped (SR_branch BC_LT (SLit 8) (SOff 10 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma grun_sc8 : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_g2 C_sc8) = (ss_c0, RS_stopped (SR_addr (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 3)) (SLit SCNT)))).
Proof. vm_compute. reflexivity. Qed.
Lemma grun_sc9 : sym_run_toN src0segs src0tbl FUEL PS_GC (add_cond ss_g2 C_sc9) = (ss_g3, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_ADD (SLit MCNT) (SAlu ALU_AND (SOff 10 0) (SLit 3))) (SLit 0)))).
Proof. vm_compute. reflexivity. Qed.
Lemma sk_g1 : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_g1) = [(Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)].
Proof. vm_compute. reflexivity. Qed.
Lemma sk_c0 : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_c0) = [(Some 33%nat, 472, 480); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)].
Proof. vm_compute. reflexivity. Qed.
Lemma sk_g3 : ss_mem ss_g3 = ss_mem ss_c0. Proof. vm_compute. reflexivity. Qed.
Lemma atoms_g1 : ss_atoms_lt 56 ss_g1 = true /\ ss_atoms_lt 57 ss_c0 = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma c0_a2 : sr_get (ss_regs ss_c0) 12 = SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 3)) (SLit SCNT) /\
sr_get (ss_regs ss_g3) 12 = SAlu ALU_ADD (SLit MCNT) (SAlu ALU_AND (SOff 10 0) (SLit 3)).
Proof. vm_compute. split; reflexivity. Qed.
Definition PS_M0 : Z := src0_A_alloc_slot + 0x580.
Definition PS_M1 : Z := src0_A_alloc_slot + 0x5ac.
Definition m0run_ (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL PS_M0 ss).
Definition m1run_ (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL PS_M1 ss).
Definition ss_ma0 : sstate := Eval vm_compute in run_ (add_cond ss_g4 C_mm).
Lemma run_mm : sym_runN src0segs src0tbl FUEL (add_cond ss_g4 C_mm) = (ss_ma0, RS_stopped (SR_branch BC_LTU (SLit 31) (SOff 10 (-7)))).
Proof. vm_compute. reflexivity. Qed.
Definition C_rin : acond := mkAC BC_GEU (SLit 31) (SOff 10 (-7)).
Definition C_rout : acond := mkAC BC_LTU (SLit 31) (SOff 10 (-7)).
Definition ss_ma1 : sstate := Eval vm_compute in m0run_ (add_cond ss_ma0 C_rin).
Lemma grun_rin : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_ma0 C_rin) = (ss_ma1, RS_stopped (SR_load (Some 10%nat) (LOCK + 881))).
Proof. vm_compute. reflexivity. Qed.
Definition R_bnc : region := mkRegion (Some 10%nat) (LOCK + 881) (LOCK + 882) (LOCK + 881) (LOCK + 882) [mkChunk (LOCK + 881) (CVal 1 (SOff 64 0))].
Definition R_usq : region := mkRegion (Some 10%nat) (LOCK + 849) (LOCK + 850) 0 0 [mkChunk (LOCK + 849) (CVal 1 (SOff 65 0))].
Definition R_seqb : region := mkRegion None (LOCK + 920) (LOCK + 921) (LOCK + 920) (LOCK + 921) [mkChunk (LOCK + 920) (CVal 1 (SOff 66 0))].
Definition R_ublk : region := mkRegion None (LOCK + 856) (LOCK + 888) (LOCK + 856) (LOCK + 888) [].
Definition F_byte : afact := mkAF 0 255 0.
Definition ss_SB : sstate := Eval vm_compute in
mkSS (ss_pc ss_ma1) (ss_regs ss_ma1) ([R_bnc; R_usq; R_seqb] ++ ss_mem ss_ma1) None
(mkFacts ((64%nat, F_byte) :: (65%nat, F_byte) :: (66%nat, F_byte) :: f_atoms (ss_facts ss_ma1)) (f_conds (ss_facts ss_ma1)) (f_alias (ss_facts ss_ma1))).
Definition ss_B_ : sstate := Eval vm_compute in m0run_ ss_SB.
Lemma grun_B_ : sym_run_toN src0segs src0tbl FUEL PS_M0 ss_SB = (ss_B_, RS_stopped (SR_branch BC_EQ (SOff 65 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_B_T : sstate := Eval vm_compute in m0run_ (add_cond ss_B_ (mkAC BC_EQ (SOff 65 0) (SLit 0))).
Lemma grun_B_T : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_B_ (mkAC BC_EQ (SOff 65 0) (SLit 0))) = (ss_B_T, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_B_F : sstate := Eval vm_compute in m0run_ (add_cond ss_B_ (mkAC BC_NE (SOff 65 0) (SLit 0))).
Lemma grun_B_F : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_B_ (mkAC BC_NE (SOff 65 0) (SLit 0))) =
(ss_B_F, RS_stopped (SR_branch BC_LT (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_B_FT : sstate := Eval vm_compute in m0run_ (add_cond ss_B_F (mkAC BC_LT (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)))).
Lemma grun_B_FT : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_B_F (mkAC BC_LT (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)))) = (ss_B_FT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_B_FF : sstate := Eval vm_compute in m0run_ (add_cond ss_B_F (mkAC BC_GE (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)))).
Lemma grun_B_FF : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_B_F (mkAC BC_GE (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)))) =
(ss_B_FF, RS_stopped (SR_branch BC_LTU (SOff 64 0) (SLit 99))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_B_FFT : sstate := Eval vm_compute in m0run_ (add_cond ss_B_FF (mkAC BC_LTU (SOff 64 0) (SLit 99))).
Lemma grun_B_FFT : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_B_FF (mkAC BC_LTU (SOff 64 0) (SLit 99))) = (ss_B_FFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_B_FFF : sstate := Eval vm_compute in m0run_ (add_cond ss_B_FF (mkAC BC_GEU (SOff 64 0) (SLit 99))).
Lemma grun_B_FFF : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_B_FF (mkAC BC_GEU (SOff 64 0) (SLit 99))) = (ss_B_FFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_mo1 : sstate := Eval vm_compute in m0run_ (add_cond ss_ma0 C_rout).
Lemma grun_rout : sym_run_toN src0segs src0tbl FUEL PS_M0 (add_cond ss_ma0 C_rout) = (ss_mo1, RS_stopped (SR_load None (LOCK + 920))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_SO : sstate := Eval vm_compute in
mkSS (ss_pc ss_mo1) (ss_regs ss_mo1) (R_seqb :: ss_mem ss_mo1) None
(mkFacts ((66%nat, F_byte) :: f_atoms (ss_facts ss_mo1)) (f_conds (ss_facts ss_mo1)) (f_alias (ss_facts ss_mo1))).
Definition ss_O_ : sstate := Eval vm_compute in m0run_ ss_SO.
Lemma grun_O_ : sym_run_toN src0segs src0tbl FUEL PS_M0 ss_SO = (ss_O_, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition M0_JUNK : list reg := [13; 15; 17; 5; 6]%bv.
Definition facts_M0 : facts := mkFacts ((67%nat, mkAF 0 1 0) :: (66%nat, F_byte) :: f_atoms (ss_facts ss_ma0)) (f_conds (ss_facts ss_ma0)) [].
Definition ss_M0 : sstate := Eval vm_compute in setfacts facts_M0 (setmem (R_seqb :: ss_mem ss_ma0) (junk_regs M0_JUNK 67 ss_B_T)).
Definition m0_check (ss : sstate) : bool := ss_atoms_lt 67 ss && mergeb ss_M0 (setfacts facts_M0 (junk_regs M0_JUNK 67 ss)).
Lemma m0_B_T : m0_check ss_B_T = true. Proof. vm_compute. reflexivity. Qed.
Lemma m0_B_FT : m0_check ss_B_FT = true. Proof. vm_compute. reflexivity. Qed.
Lemma m0_B_FFT : m0_check ss_B_FFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma m0_B_FFF : m0_check ss_B_FFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma m0_O_ : m0_check ss_O_ = true. Proof. vm_compute. reflexivity. Qed.
Lemma ss_M0_pc : ss_pc ss_M0 = PS_M0. Proof. reflexivity. Qed.
Definition leafA (ss : sstate) : sv * option cval :=
(sr_get (ss_regs ss) 13, match ss_mem ss with r :: _ => match r_chunks r with c :: _ => Some (c_val c) | _ => None end | _ => None end).
Lemma leafA_vals : leafA ss_B_T = (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 64 0) (SLit 100)) (SLit 1), Some (CVal 1 (SOff 64 0)))
/\ leafA ss_B_FT = (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 64 0) (SLit 100)) (SLit 1), Some (CVal 1 (SOff 64 0)))
/\ leafA ss_B_FFT = (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 64 0) (SLit 100)) (SLit 1), Some (CVal 1 (SOff 64 1)))
/\ leafA ss_B_FFF = (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 64 0) (SLit 100)) (SLit 1), Some (CVal 1 (SLit 150)))
/\ sr_get (ss_regs ss_O_) 13 = SLit 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition ss_m0a : sstate := Eval vm_compute in m1run_ ss_M0.
Lemma grun_M0 : sym_run_toN src0segs src0tbl FUEL PS_M1 ss_M0 = (ss_m0a, RS_stopped (SR_branch BC_NE (SOff 66 0) (SLit 255))).
Proof. vm_compute. reflexivity. Qed.
Definition C_sne : acond := mkAC BC_NE (SOff 66 0) (SLit 255).
Definition C_s255 : acond := mkAC BC_EQ (SOff 66 0) (SLit 255).
Definition ss_mA : sstate := Eval vm_compute in m1run_ (add_cond ss_m0a C_sne).
Lemma grun_mA : sym_run_toN src0segs src0tbl FUEL PS_M1 (add_cond ss_m0a C_sne) = (ss_mA, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_mB0 : sstate := Eval vm_compute in m1run_ (add_cond ss_m0a C_s255).
Lemma grun_mB0 : sym_run_toN src0segs src0tbl FUEL PS_M1 (add_cond ss_m0a C_s255) = (ss_mB0, RS_stopped (SR_store None (LOCK + 856))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_SU : sstate := Eval vm_compute in mkSS (ss_pc ss_mB0) (ss_regs ss_mB0) (R_ublk :: ss_mem ss_mB0) None (ss_facts ss_mB0).
Definition ss_mB : sstate := Eval vm_compute in m1run_ ss_SU.
Lemma grun_mB : sym_run_toN src0segs src0tbl FUEL PS_M1 ss_SU = (ss_mB, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition M1_JUNK : list reg := [16]%bv.
Definition ss_M1 : sstate := Eval vm_compute in setfacts facts_M0 (setmem (ss_mem ss_ma0) (junk_regs M1_JUNK 72 ss_mA)).
Definition m1_check (ss : sstate) : bool := ss_atoms_lt 72 ss && mergeb ss_M1 (setfacts facts_M0 (junk_regs M1_JUNK 72 ss)).
Lemma m1_A : m1_check ss_mA = true. Proof. vm_compute. reflexivity. Qed.
Lemma m1_B : m1_check ss_mB = true. Proof. vm_compute. reflexivity. Qed.
Lemma ss_M1_pc : ss_pc ss_M1 = PS_M1. Proof. reflexivity. Qed.
Lemma leafM1_vals :
firstn 1 (ss_mem ss_mA) = [mkRegion None (LOCK + 920) (LOCK + 921) (LOCK + 920) (LOCK + 921) [mkChunk (LOCK + 920) (CVal 1 (SOff 66 1))]] /\
firstn 2 (ss_mem ss_mB) = [mkRegion None (LOCK + 856) (LOCK + 888) (LOCK + 856) (LOCK + 888)
[mkChunk (LOCK + 880) (CVal 8 (SLit 0)); mkChunk (LOCK + 872) (CVal 8 (SLit 0)); mkChunk (LOCK + 864) (CVal 8 (SLit 0)); mkChunk (LOCK + 856) (CVal 8 (SLit 0))];
mkRegion None (LOCK + 920) (LOCK + 921) (LOCK + 920) (LOCK + 921) [mkChunk (LOCK + 920) (CVal 1 (SLit 1))]].
Proof. vm_compute. split; reflexivity. Qed.
Lemma M1_regs : regs_at ss_M1 [1; 2; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 41 0; SOff 2 (-144); SLit TP; SOff 10 0; SOff 40 0; SOff 56 0; SLit 4096; SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16); SOff 67 0; SOff 62 0;
SOff 11 0; SOff 61 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SAlu ALU_SLL (SOff 35 0) (SLit 4); SLit SCT; SOff 26 0; SOff 27 0].
Proof. vm_compute. reflexivity. Qed.
End a.
