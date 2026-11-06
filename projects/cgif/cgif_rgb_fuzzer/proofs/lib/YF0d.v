(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YF0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0c YQ0b YQ03 YQ0i YQ09 YQ04 YQ0e YQ0f YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Definition tfxtbl_rtD {imgk : img} : ctable := ltac:(img_eval_sel (fun imgk : img => (build_table tfxsegs (0x72d40 + D_2c4) 36%nat tfxtbl_rtB))).
Lemma tfxtbl_rtD_eq {imgk : img} : tfxtbl_rtD = build_table tfxsegs (0x72d40 + D_2c4) 36%nat tfxtbl_rtB.
Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl _ l_) end. Qed.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma tfxtbl_rtD_ok {imgk : img} : table_ok tfxsegs tfxtbl_rtD.
Proof. img_destruct imgk. all: rewrite tfxtbl_rtD_eq. all: img_apply build_table_ok; [img_try ((img_case; cbv); discriminate) | img_try (img_exact tfxtbl_rtB_ok)]. Qed.
End b.
Definition aNB : nat := 32.  Definition aSB : nat := 33.  Definition aTOT : nat := 34.  Definition aN : nat := 35.
Definition aHASH : nat := 36. Definition aS2 : nat := 37. Definition aHD : nat := 38.  Definition aSTD : nat := 39.
Definition aNDN : nat := 40. Definition aSLOT : nat := 41. Definition K_D : nat := 42.
Definition u64f : afact := mkAF 0 (2 ^ 64 - 1) 0.
Definition DF_fixed {imgk : img} : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + DEP_STK) kHighMemEnd 4); (10%nat, mkAF kHighMemBeg (kHighMemEnd - 240) 3); (11%nat, mkAF 1 30 0);
(aNB, mkAF 4096 (CEIL_MAX - kNodesBlockSize) 12); (aSB, mkAF 4096 (CEIL_MAX - kStoreBlockSize) 12);
(aTOT, mkAF 2 131072 0); (aN, mkAF 1 4097 0); (aHASH, u64f); (aS2, mkAF TFX_DEPOT (TFX_DEPOT + 4 * 2 ^ 20 - 4) 2);
(aHD, mkAF 0 4097 0); (aSTD, mkAF 0 (2 ^ 32 - 1) 0); (aNDN, mkAF 4096 CEIL_MAX 4); (aSLOT, mkAF 4096 CEIL_MAX 3) ].
Definition DF0 {imgk : img} : facts := mkFacts DF_fixed [] [].
Definition lit8 (a v : Z) : YQ0b.region := YQ0b.mkRegion None a (a + 8) 0 0 [YQ0b.mkChunk a (CVal 8 (SLit v))].
Definition cell8 (a : Z) (n : nat) : YQ0b.region := YQ0b.mkRegion None a (a + 8) a (a + 8) [YQ0b.mkChunk a (CVal 8 (SOff n 0))].
Definition cell8r (a : Z) (n : nat) : YQ0b.region := YQ0b.mkRegion None a (a + 8) 0 0 [YQ0b.mkChunk a (CVal 8 (SOff n 0))].
Definition cell4 (a : Z) (n : nat) : YQ0b.region := YQ0b.mkRegion None a (a + 4) a (a + 4) [YQ0b.mkChunk a (CVal 4 (SOff n 0))].
Definition R_DS : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- DEP_STK) 0 (- DEP_STK) 0 [].
Definition D_consts {imgk : img} : smem := [ lit8 0x102e8 DH_M; lit8 (0x10308 + D_8) DH_M8; lit8 (0x103a0 + D_20) DH_SEED ].
Definition R_MAP1 {imgk : img} : YQ0b.region := cell8r (TFX_DEPOT + d_map1) aNB.
Definition R_NUNIQ {imgk : img} : YQ0b.region := cell4 (TFX_DEPOT + d_nuniq) aN.
Definition R_TAB : YQ0b.region := YQ0b.mkRegion (Some aS2) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff aHD 0))].
Definition R_TOT {imgk : img} : YQ0b.region := cell8 TFX_STORE aTOT.
Definition R_SBC {imgk : img} : YQ0b.region := cell8r (TFX_STORE + 16) aSB.
Definition R_STD {imgk : img} : YQ0b.region := cell4 (TFX_STORE + 24) aSTD.
Definition R_NODE : YQ0b.region := YQ0b.mkRegion (Some aNDN) 0 16 0 16 [].
Definition R_SLOT : YQ0b.region := YQ0b.mkRegion (Some aSLOT) 0 248 0 248 [].
Definition D_cf {imgk : img} : smem := [ lit8 (0xa2150 + D_10f0) (0x13bce8 + D_10c0); lit8 (0x13bdd8 + D_10c0) 0x101000100000000 ].
Definition DFIX {imgk : img} : smem := D_consts ++ [R_MAP1; R_NUNIQ; R_TAB; R_TOT; R_SBC; R_STD; R_NODE; R_SLOT] ++ D_cf.
Definition DMEM0 {imgk : img} : smem := R_DS :: DFIX.
Definition DREGS0 {imgk : img} : list sv := sr_set (sr_set sr_atoms 4%bv (SLit TFX_TP)) 3%bv (SLit TFX_GP).
Definition SS_D0 {imgk : img} : sstate := mkSS A_StackDepotPut DREGS0 DMEM0 None DF0.
Definition run_d {imgk : img} (ss : sstate) : sstate := fst (sym_runN tfxsegs tfxtbl_rtD FUEL ss).
Definition runto_d {imgk : img} (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfxsegs tfxtbl_rtD FUEL pc ss).
Definition A_HLOOP {imgk : img} : Z := (0x7307c + D_2c4).
Definition S_H0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto_d A_HLOOP SS_D0))).
Definition dW : nat := 42. Definition dH : nat := 43. Definition dP : nat := 44. Definition dE : nat := 45.
Definition R_W : YQ0b.region := YQ0b.mkRegion (Some dP) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff dW 0))].
Definition HREGS {imgk : img} : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (ss_regs S_H0) 11%bv (SOff dP 0)) 12%bv (SOff dH 0)) 13%bv (SLit 0)) 14%bv (SOff dE 0))
15%bv (SOff 46%nat 0)) 16%bv (SOff 47%nat 0).
Definition HATOMS {imgk : img} : list (nat * afact) :=
DF_fixed ++ [(dW, u64f); (dH, u64f); (dP, mkAF kHighMemBeg (kHighMemEnd - 8) 3); (dE, mkAF kHighMemBeg kHighMemEnd 3); (46%nat, u64f); (47%nat, u64f)].
Definition HF {imgk : img} : facts := mkFacts HATOMS [] [].
Definition R_DS' {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd R_DS (ss_mem S_H0)))).
Definition DFIX' {imgk : img} : smem := R_DS' :: DFIX.
Definition S_H {imgk : img} : sstate := mkSS A_HLOOP HREGS (R_W :: DFIX') None HF.
Definition S_HT {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d S_H))).
Definition c_hloop : acond := mkAC Instr.BC_NE (SOff dP 8) (SOff dE 0).
Definition c_hexit : acond := mkAC Instr.BC_EQ (SOff dP 8) (SOff dE 0).
Definition S_HX {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_HT c_hexit)))).
Definition A_BKT {imgk : img} : Z := (0x730ec + D_2c4).
Definition BREGS {imgk : img} : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (ss_regs S_HX) 19%bv (SOff aHASH 0)) 18%bv (SOff aS2 0)) 10%bv (SOff 42%nat 0))
11%bv (SOff 43%nat 0)) 12%bv (SOff 44%nat 0)) 14%bv (SOff 45%nat 0)) 15%bv (SOff 46%nat 0)) 16%bv (SOff 47%nat 0).
Definition BATOMS {imgk : img} : list (nat * afact) := DF_fixed ++ [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f); (46%nat, u64f); (47%nat, u64f)].
Definition BFc {imgk : img} : facts := mkFacts BATOMS [] [].
Definition S_B {imgk : img} : sstate := mkSS A_BKT BREGS DFIX' None BFc.
Definition S_BF {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d S_B))).
Definition aID : nat := 42. Definition aND : nat := 43. Definition aNH : nat := 44. Definition aNL : nat := 45.
Definition A_FLOOP {imgk : img} : Z := (0x7310c + D_2c4).
Definition A_FNODE {imgk : img} : Z := (0x7313c + D_2c4).
Definition FLREGS {imgk : img} : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (ss_regs S_BF) 11%bv (SOff aID 0)) 25%bv (SOff aHD 0)) 10%bv (SOff 49%nat 0)) 12%bv (SOff 50%nat 0))
14%bv (SOff 46%nat 0)) 15%bv (SOff 47%nat 0)) 16%bv (SOff 48%nat 0).
Definition FLATOMS {imgk : img} : list (nat * afact) := DF_fixed ++ [(aID, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f); (49%nat, u64f); (50%nat, u64f)].
Definition FLc {imgk : img} : facts := mkFacts FLATOMS [] [].
Definition FATOMS {imgk : img} : list (nat * afact) :=
DF_fixed ++ [(aID, mkAF 0 4097 0); (aND, mkAF 4096 CEIL_MAX 4)  ; (aNH, u64f); (aNL, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f)].
Definition FFc {imgk : img} : facts := mkFacts FATOMS [] [].
Definition S_FL {imgk : img} : sstate := mkSS A_FLOOP FLREGS DFIX' None FLc.
Definition R_ND : YQ0b.region :=
YQ0b.mkRegion (Some aND) 0 12 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff aNH 0)); YQ0b.mkChunk 8 (CVal 4 (SOff aNL 0))].
Definition FNREGS {imgk : img} : list sv := sr_set (sr_set (sr_set FLREGS 10%bv (SOff aID 0)) 11%bv (SOff aND 0)) 12%bv (SOff aNB 0).
Definition S_FN {imgk : img} : sstate := mkSS A_FNODE FNREGS (R_ND :: DFIX') None FFc.
Definition c_fl0 : acond := mkAC Instr.BC_EQ (SOff aID 0) (SLit 0).
Definition c_flnz : acond := mkAC Instr.BC_NE (SOff aID 0) (SLit 0).
Definition S_FL1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_FL c_flnz)))).
Definition S_FL2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (mkSS (ss_pc S_FL1) (sr_set (ss_regs S_FL1) 12%bv (SLit (TFX_DEPOT + d_map1))) (ss_mem S_FL1) None (ss_facts S_FL1))))).
Definition S_FNT {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d S_FN))).
Definition c_found : acond := mkAC Instr.BC_EQ (SOff aHASH 0) (SOff aNH 0).
Definition c_fnext : acond := mkAC Instr.BC_NE (SOff aHASH 0) (SOff aNH 0).
Definition S_FOUND {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_FNT c_found)))).
Definition S_FNX {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_FNT c_fnext)))).
Definition S_MISS {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_FL c_fl0)))).
Definition aSC : nat := 42. Definition aDC : nat := 43. Definition aME : nat := 44. Definition aBY : nat := 45.
Definition A_MC {imgk : img} : Z := (0x64414 + D_2c4).
Definition R_SRC : YQ0b.region := YQ0b.mkRegion (Some aSC) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff aBY 0))].
Definition R_DST : YQ0b.region := YQ0b.mkRegion (Some aDC) 0 1 0 1 [].
Definition no_slot (r : YQ0b.region) : bool := match YQ0b.r_base r with Some 41%nat => false | _ => true end.
Definition run_dsh {imgk : img} (ss : sstate) : sstate := fst (sym_runN_sh tfxsegs tfxtbl_rtD FUEL ss).
Definition pin (ss : sstate) (r : bv 5) (e : sv) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) None (ss_facts ss).
Definition S_I1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh S_MISS))).
Definition S_I2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (pin S_I1 10%bv (SLit (TFX_DEPOT + d_map1)))))).
Definition S_I3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (pin (pin (pin S_I2 10%bv (SOff aNDN 0)) 8%bv (SOff aNDN 0)) 9%bv (SOff aNDN 0))))).
Definition S_I4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (pin (pin S_I3 21%bv (SLit 0)) 11%bv (SOff 11%nat 0))))).
Definition S_I5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (pin (pin S_I4 5%bv (SLit 0)) 6%bv (SLit 0))))).
Definition c_i5 : acond := mkAC Instr.BC_EQ (SAlu Instr.ALU_SRL (SOff aTOT 0) (SLit 32)) (SLit 0).
Definition S_I6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (add_cond S_I5 c_i5)))).
Definition S_I7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (pin S_I6 10%bv (SOff aSLOT 0))))).
Definition c_i7 : acond := mkAC Instr.BC_NE (SAlu Instr.ALU_SLL (SOff 11%nat 0) (SLit 3)) (SLit 0).
Definition S_I8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (add_cond S_I7 c_i7)))).
Definition MCREGS {imgk : img} : list sv := sr_set (sr_set (sr_set (sr_set (ss_regs S_I8) 11%bv (SOff aSC 0)) 13%bv (SOff aDC 0)) 12%bv (SOff aME 0)) 14%bv (SOff 46%nat 0).
Definition MCATOMS {imgk : img} : list (nat * afact) :=
DF_fixed ++ [(aSC, mkAF kHighMemBeg kHighMemEnd 0); (aDC, mkAF 4096 CEIL_MAX 0); (aME, mkAF 4096 CEIL_MAX 0)  ; (aBY, mkAF 0 255 0); (46%nat, u64f); (48%nat, u64f)].
Definition MCF {imgk : img} : facts := mkFacts MCATOMS [] [].
Definition MCFIX {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (filter no_slot (ss_mem S_I8)))).
Definition S_MC {imgk : img} : sstate := mkSS A_MC MCREGS (R_SRC :: R_DST :: MCFIX) None MCF.
Definition S_MCT {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d S_MC))).
Definition c_mcloop : acond := mkAC Instr.BC_NE (SOff aDC 1) (SOff aME 0).
Definition c_mcexit : acond := mkAC Instr.BC_EQ (SOff aDC 1) (SOff aME 0).
Definition S_T1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_MCT c_mcexit)))).
Definition S_T2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_dsh (pin S_T1 10%bv (SLit (TFX_STORE + 24)))))).
Definition X_PACK {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs S_T2) 11%bv))).
Definition c_pk0 {imgk : img} : acond := mkAC Instr.BC_EQ X_PACK (SLit 0).
Definition c_pk1 {imgk : img} : acond := mkAC Instr.BC_NE X_PACK (SLit 0).
Definition S_TE0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_T2 c_pk0)))).
Definition S_TE1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_d (add_cond S_T2 c_pk1)))).
Definition A_END {imgk : img} : Z := (0x73240 + D_2c4).
Definition ENDREGS {imgk : img} : list sv := sr_set (sr_set (sr_set (sr_set (ss_regs S_TE0) 11%bv (SOff 42%nat 0)) 13%bv (SOff 43%nat 0)) 14%bv (SOff 44%nat 0)) 16%bv (SOff 45%nat 0).
Definition ENDMEM {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => ((R_DS :: skipn 3 (ss_mem S_TE0))))).
Definition ENDF {imgk : img} : facts := mkFacts (DF_fixed ++ [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f)]) [] [].
Definition S_END {imgk : img} : sstate := mkSS A_END ENDREGS ENDMEM None ENDF.
