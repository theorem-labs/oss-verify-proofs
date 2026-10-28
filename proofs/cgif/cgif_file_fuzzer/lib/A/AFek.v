(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Export YF0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma tfib_dhash_tr0 : forall h, (h < 2)%nat -> tfib_dhash (TFIB_TR0 h) = TFIB_HASH h.
Proof. intros [|[|h]] Hh; [vm_compute; reflexivity | vm_compute; reflexivity | lia]. Qed.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP06 YP03 YP0g YP0i YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AFl0.
Definition tfibtbl_rtD : ctable := Eval vm_compute in build_table tfibsegs 0x72224 36%nat tfibtbl_rtB.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = build_table tfibsegs 0x72224 36%nat tfibtbl_rtB.
Proof. vm_cast_no_check (eq_refl tfibtbl_rtD). Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. apply build_table_ok; [cbv; discriminate | exact tfibtbl_rtB_ok]. Qed.
End b.
Definition aNB : nat := 32.  Definition aSB : nat := 33.  Definition aTOT : nat := 34.  Definition aN : nat := 35.
Definition aHASH : nat := 36. Definition aS2 : nat := 37. Definition aHD : nat := 38.  Definition aSTD : nat := 39.
Definition aNDN : nat := 40. Definition aSLOT : nat := 41. Definition K_D : nat := 42.
Definition u64f : afact := mkAF 0 (2 ^ 64 - 1) 0.
Definition DF_fixed : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + DEP_STK) kHighMemEnd 4); (10%nat, mkAF kHighMemBeg (kHighMemEnd - 240) 3); (11%nat, mkAF 1 30 0);
(aNB, mkAF 4096 (CEIL_MAX - kNodesBlockSize) 12); (aSB, mkAF 4096 (CEIL_MAX - kStoreBlockSize) 12);
(aTOT, mkAF 2 131072 0); (aN, mkAF 1 4097 0); (aHASH, u64f); (aS2, mkAF TFIB_DEPOT (TFIB_DEPOT + 4 * 2 ^ 20 - 4) 2);
(aHD, mkAF 0 4097 0); (aSTD, mkAF 0 (2 ^ 32 - 1) 0); (aNDN, mkAF 4096 CEIL_MAX 4); (aSLOT, mkAF 4096 CEIL_MAX 3) ].
Definition DF0 : facts := mkFacts DF_fixed [] [].
Definition lit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition cell8 (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 8) a (a + 8) [YP09.mkChunk a (CVal 8 (SOff n 0))].
Definition cell8r (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SOff n 0))].
Definition cell4 (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 4) a (a + 4) [YP09.mkChunk a (CVal 4 (SOff n 0))].
Definition R_DS : YP09.region := YP09.mkRegion (Some 2%nat) (- DEP_STK) 0 (- DEP_STK) 0 [].
Definition D_consts : smem := [ lit8 0x102e8 DH_M; lit8 0x10308 DH_M8; lit8 0x10398 DH_SEED ].
Definition R_MAP1 : YP09.region := cell8r (TFIB_DEPOT + d_map1) aNB.
Definition R_NUNIQ : YP09.region := cell4 (TFIB_DEPOT + d_nuniq) aN.
Definition R_TAB : YP09.region := YP09.mkRegion (Some aS2) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff aHD 0))].
Definition R_TOT : YP09.region := cell8 TFIB_STORE aTOT.
Definition R_SBC : YP09.region := cell8r (TFIB_STORE + 16) aSB.
Definition R_STD : YP09.region := cell4 (TFIB_STORE + 24) aSTD.
Definition R_NODE : YP09.region := YP09.mkRegion (Some aNDN) 0 16 0 16 [].
Definition R_SLOT : YP09.region := YP09.mkRegion (Some aSLOT) 0 248 0 248 [].
Definition D_cf : smem := [ lit8 0x9df88 0x137b28; lit8 0x137c18 0x101000100000000 ].
Definition DFIX : smem := D_consts ++ [R_MAP1; R_NUNIQ; R_TAB; R_TOT; R_SBC; R_STD; R_NODE; R_SLOT] ++ D_cf.
Definition DMEM0 : smem := R_DS :: DFIX.
Definition DREGS0 : list sv := sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 3%bv (SLit TFIB_GP).
Definition SS_D0 : sstate := mkSS A_StackDepotPut DREGS0 DMEM0 None DF0.
Definition run_d (ss : sstate) : sstate := fst (sym_runN tfibsegs tfibtbl_rtD FUEL ss).
Definition runto_d (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfibsegs tfibtbl_rtD FUEL pc ss).
Definition A_HLOOP : Z := 0x72560.
Definition S_H0 : sstate := Eval vm_compute in runto_d A_HLOOP SS_D0.
Definition dW : nat := 42. Definition dH : nat := 43. Definition dP : nat := 44. Definition dE : nat := 45.
Definition R_W : YP09.region := YP09.mkRegion (Some dP) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff dW 0))].
Definition HREGS : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (ss_regs S_H0) 11%bv (SOff dP 0)) 12%bv (SOff dH 0)) 13%bv (SLit 0)) 14%bv (SOff dE 0))
15%bv (SOff 46%nat 0)) 16%bv (SOff 47%nat 0).
Definition HATOMS : list (nat * afact) :=
DF_fixed ++ [(dW, u64f); (dH, u64f); (dP, mkAF kHighMemBeg (kHighMemEnd - 8) 3); (dE, mkAF kHighMemBeg kHighMemEnd 3); (46%nat, u64f); (47%nat, u64f)].
Definition HF : facts := mkFacts HATOMS [] [].
Definition R_DS' : YP09.region := Eval vm_compute in hd R_DS (ss_mem S_H0).
Definition DFIX' : smem := R_DS' :: DFIX.
Definition S_H : sstate := mkSS A_HLOOP HREGS (R_W :: DFIX') None HF.
Definition S_HT : sstate := Eval vm_compute in run_d S_H.
Definition c_hloop : acond := mkAC Instr.BC_NE (SOff dP 8) (SOff dE 0).
Definition c_hexit : acond := mkAC Instr.BC_EQ (SOff dP 8) (SOff dE 0).
Definition S_HX : sstate := Eval vm_compute in run_d (add_cond S_HT c_hexit).
Definition A_BKT : Z := 0x725d0.
Definition BREGS : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (ss_regs S_HX) 19%bv (SOff aHASH 0)) 18%bv (SOff aS2 0)) 10%bv (SOff 42%nat 0))
11%bv (SOff 43%nat 0)) 12%bv (SOff 44%nat 0)) 14%bv (SOff 45%nat 0)) 15%bv (SOff 46%nat 0)) 16%bv (SOff 47%nat 0).
Definition BATOMS : list (nat * afact) := DF_fixed ++ [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f); (46%nat, u64f); (47%nat, u64f)].
Definition BFc : facts := mkFacts BATOMS [] [].
Definition S_B : sstate := mkSS A_BKT BREGS DFIX' None BFc.
Definition S_BF : sstate := Eval vm_compute in run_d S_B.
Definition aID : nat := 42. Definition aND : nat := 43. Definition aNH : nat := 44. Definition aNL : nat := 45.
Definition A_FLOOP : Z := 0x725f0.
Definition A_FNODE : Z := 0x72620.
Definition FLREGS : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (ss_regs S_BF) 11%bv (SOff aID 0)) 25%bv (SOff aHD 0)) 10%bv (SOff 49%nat 0)) 12%bv (SOff 50%nat 0))
14%bv (SOff 46%nat 0)) 15%bv (SOff 47%nat 0)) 16%bv (SOff 48%nat 0).
Definition FLATOMS : list (nat * afact) := DF_fixed ++ [(aID, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f); (49%nat, u64f); (50%nat, u64f)].
Definition FLc : facts := mkFacts FLATOMS [] [].
Definition FATOMS : list (nat * afact) :=
DF_fixed ++ [(aID, mkAF 0 4097 0); (aND, mkAF 4096 CEIL_MAX 4)  ; (aNH, u64f); (aNL, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f)].
Definition FFc : facts := mkFacts FATOMS [] [].
Definition S_FL : sstate := mkSS A_FLOOP FLREGS DFIX' None FLc.
Definition R_ND : YP09.region :=
YP09.mkRegion (Some aND) 0 12 0 0 [YP09.mkChunk 0 (CVal 8 (SOff aNH 0)); YP09.mkChunk 8 (CVal 4 (SOff aNL 0))].
Definition FNREGS : list sv := sr_set (sr_set (sr_set FLREGS 10%bv (SOff aID 0)) 11%bv (SOff aND 0)) 12%bv (SOff aNB 0).
Definition S_FN : sstate := mkSS A_FNODE FNREGS (R_ND :: DFIX') None FFc.
Definition c_fl0 : acond := mkAC Instr.BC_EQ (SOff aID 0) (SLit 0).
Definition c_flnz : acond := mkAC Instr.BC_NE (SOff aID 0) (SLit 0).
Definition S_FL1 : sstate := Eval vm_compute in run_d (add_cond S_FL c_flnz).
Definition S_FL2 : sstate := Eval vm_compute in run_d (mkSS (ss_pc S_FL1) (sr_set (ss_regs S_FL1) 12%bv (SLit (TFIB_DEPOT + d_map1))) (ss_mem S_FL1) None (ss_facts S_FL1)).
Definition S_FNT : sstate := Eval vm_compute in run_d S_FN.
Definition c_found : acond := mkAC Instr.BC_EQ (SOff aHASH 0) (SOff aNH 0).
Definition c_fnext : acond := mkAC Instr.BC_NE (SOff aHASH 0) (SOff aNH 0).
Definition S_FOUND : sstate := Eval vm_compute in run_d (add_cond S_FNT c_found).
Definition S_FNX : sstate := Eval vm_compute in run_d (add_cond S_FNT c_fnext).
Definition S_MISS : sstate := Eval vm_compute in run_d (add_cond S_FL c_fl0).
Definition aSC : nat := 42. Definition aDC : nat := 43. Definition aME : nat := 44. Definition aBY : nat := 45.
Definition A_MC : Z := 0x638f8.
Definition R_SRC : YP09.region := YP09.mkRegion (Some aSC) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff aBY 0))].
Definition R_DST : YP09.region := YP09.mkRegion (Some aDC) 0 1 0 1 [].
Definition no_slot (r : YP09.region) : bool := match YP09.r_base r with Some 41%nat => false | _ => true end.
Definition run_dsh (ss : sstate) : sstate := fst (sym_runN_sh tfibsegs tfibtbl_rtD FUEL ss).
Definition pin (ss : sstate) (r : bv 5) (e : sv) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) None (ss_facts ss).
Definition S_I1 : sstate := Eval vm_compute in run_dsh S_MISS.
Definition S_I2 : sstate := Eval vm_compute in run_dsh (pin S_I1 10%bv (SLit (TFIB_DEPOT + d_map1))).
Definition S_I3 : sstate := Eval vm_compute in run_dsh (pin (pin (pin S_I2 10%bv (SOff aNDN 0)) 8%bv (SOff aNDN 0)) 9%bv (SOff aNDN 0)).
Definition S_I4 : sstate := Eval vm_compute in run_dsh (pin (pin S_I3 21%bv (SLit 0)) 11%bv (SOff 11%nat 0)).
Definition S_I5 : sstate := Eval vm_compute in run_dsh (pin (pin S_I4 5%bv (SLit 0)) 6%bv (SLit 0)).
Definition c_i5 : acond := mkAC Instr.BC_EQ (SAlu Instr.ALU_SRL (SOff aTOT 0) (SLit 32)) (SLit 0).
Definition S_I6 : sstate := Eval vm_compute in run_dsh (add_cond S_I5 c_i5).
Definition S_I7 : sstate := Eval vm_compute in run_dsh (pin S_I6 10%bv (SOff aSLOT 0)).
Definition c_i7 : acond := mkAC Instr.BC_NE (SAlu Instr.ALU_SLL (SOff 11%nat 0) (SLit 3)) (SLit 0).
Definition S_I8 : sstate := Eval vm_compute in run_dsh (add_cond S_I7 c_i7).
Definition MCREGS : list sv := sr_set (sr_set (sr_set (sr_set (ss_regs S_I8) 11%bv (SOff aSC 0)) 13%bv (SOff aDC 0)) 12%bv (SOff aME 0)) 14%bv (SOff 46%nat 0).
Definition MCATOMS : list (nat * afact) :=
DF_fixed ++ [(aSC, mkAF kHighMemBeg kHighMemEnd 0); (aDC, mkAF 4096 CEIL_MAX 0); (aME, mkAF 4096 CEIL_MAX 0)  ; (aBY, mkAF 0 255 0); (46%nat, u64f); (48%nat, u64f)].
Definition MCF : facts := mkFacts MCATOMS [] [].
Definition MCFIX : smem := Eval vm_compute in filter no_slot (ss_mem S_I8).
Definition S_MC : sstate := mkSS A_MC MCREGS (R_SRC :: R_DST :: MCFIX) None MCF.
Definition S_MCT : sstate := Eval vm_compute in run_d S_MC.
Definition c_mcloop : acond := mkAC Instr.BC_NE (SOff aDC 1) (SOff aME 0).
Definition c_mcexit : acond := mkAC Instr.BC_EQ (SOff aDC 1) (SOff aME 0).
Definition S_T1 : sstate := Eval vm_compute in run_d (add_cond S_MCT c_mcexit).
Definition S_T2 : sstate := Eval vm_compute in run_dsh (pin S_T1 10%bv (SLit (TFIB_STORE + 24))).
Definition X_PACK : sv := Eval vm_compute in sr_get (ss_regs S_T2) 11%bv.
Definition c_pk0 : acond := mkAC Instr.BC_EQ X_PACK (SLit 0).
Definition c_pk1 : acond := mkAC Instr.BC_NE X_PACK (SLit 0).
Definition S_TE0 : sstate := Eval vm_compute in run_d (add_cond S_T2 c_pk0).
Definition S_TE1 : sstate := Eval vm_compute in run_d (add_cond S_T2 c_pk1).
Definition A_END : Z := 0x72724.
Definition ENDREGS : list sv := sr_set (sr_set (sr_set (sr_set (ss_regs S_TE0) 11%bv (SOff 42%nat 0)) 13%bv (SOff 43%nat 0)) 14%bv (SOff 44%nat 0)) 16%bv (SOff 45%nat 0).
Definition ENDMEM : smem := Eval vm_compute in (R_DS :: skipn 3 (ss_mem S_TE0)).
Definition ENDF : facts := mkFacts (DF_fixed ++ [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f)]) [] [].
Definition S_END : sstate := mkSS A_END ENDREGS ENDMEM None ENDF.
