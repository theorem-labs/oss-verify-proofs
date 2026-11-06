(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec fx.

(* [comment removed for export] *)
Module Icpt_read_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "ACEIL"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "sub"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "valuation"; "holds"; "eval"; "reg_sv"; "cell"; "ss_facts"; "SLit"; "sv"; "agree_below"; "sobj"; "sprop_below"; "SPBranch"; "DUnknown"; "SPNot"; "mkObj"; "soff"; "ss_next"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "list"; "nil"; "Some"; "option"; "app"; "bool"; "true"; "cons"; "prod"; "length"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read"; "E_ecall"; "Fpos"; "Posts_rd"; "buf"; "Pre_rd"; "vC"; "FR"; "F_L"; "Posts_rd_d"; "cur"; "hc"; "gl"; "gs"; "E_reg"; "F8of"; "T_rd_d"; "lastb"; "s_L_bk"; "s_L_in"; "E_L_bk"; "E_L_in"; "E_pos"; "base_rd"; "vBb"; "vLb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "ok_frameA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "fd_lookup"; "m_fds"; "FdFile"; "m_fs"; "FdDir"; "MAX_RW_COUNT"; "TASK_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_read_proof"; "rdZ"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "shp"; "add"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "BC_GEU"; "BC_NE"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA"; "A_after_fresh"; "A_after_hdr"; "rbA_md'"; "rhA_rho'"; "rkA_rho'"; "rbA_bs"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_read_proof.BaseZ"; "rdZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "withGA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL SysRead.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr RDAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Section BaseZ.
Variable rho : valuation.
Let B := bv_unsigned (rw rho 15). Let L := bv_unsigned (rw rho 16). Let O := bv_unsigned (rw rho 17). Let C := bv_unsigned (rw rho 19).

Definition rdZ : Prop := ltac2:(tb__ "0|7|
S2bS5S6VO;VC;A2VL;A2S2bS5VL;S9Z2M0Z28A2A2S2bS5Z1000M1VB;A2S2bS5S6VB;VL;A2SaS9G0Z2fA2M2Z8M3A2A2S2bS2cS47SbVB;G3A2Z0A3S2bS2bS5Z1VC;A2S5VC;Z10000A2A2S2bS2bS5S6S1G1A2S2Q40M4SdVrho;PaA2A2M5A2S5G5S9G0Z3fA2A2A2S2bS5G1S2G4SdVrho;P18A2A2M6A2S5G6G2A2A2A2A2A2A2A2A2A2").

Lemma base_rd_Z : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S44A3S75F_;").
Proof.
  intros HF.
  pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho 19)) as R19. pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 24)) as R24.
  have_fact A1 HF (SPUle (add vOb vC) vLb). have_fact A2 HF (SPUle vLb (SLit (2 ^ 40))). have_fact A3 HF (SPUle (SLit 4096) vBb).
  have_fact A4 HF (SPUle (add vBb vLb) (SLit (2 ^ 47 - 8))). have_fact A5 HF (SPAlign 15 3).
  have_fact A6 HF (SPUle (SLit 1) vC). have_fact A7 HF (SPUle vC (SLit 65536)).
  have_fact A8 HF (SPUle (SLit (ACEIL + 4096)) (SVar 10)). have_fact A9 HF (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact A10 HF (SPUle (SLit 4096) (SVar 24)). have_fact A11 HF (SPUle (SVar 24) (SLit (2 ^ 47))).
  have_fact A12 HF (SPUle vOb vLb). have_fact A13 HF (SPUle vC vLb). have_fact A14 HF (SPUle vBb (SLit (2 ^ 47 - 8))).
  unfold vBb, vLb, vOb, vC, add in A1, A2, A3, A4, A6, A7, A12, A13, A14.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 4096) in A3 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as T47. rewrite T47 in A4. rewrite T47 in A14.
  rewrite (U_lit64 rho 1) in A6 by lia. rewrite (U_lit64 rho 65536) in A7 by lia.
  rewrite (U_lit64 rho (ACEIL + 4096)) in A8 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in A9 by lia.
  rewrite (U_lit64 rho 4096) in A10 by lia. rewrite (U_lit64 rho (2 ^ 47)) in A11 by lia.
  cbn [eval] in A2, A3, A6, A7, A8, A9, A10, A11, A12, A13, A14.
  assert (B1 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho 19) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar 19) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho 19)) eq_refl eq_refl B1) in A1. cbn [eval] in A1.
  assert (B2 : 0 <= bv_unsigned (rw rho 15) + bv_unsigned (rw rho 16) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 15) (SVar 16) (bv_unsigned (rw rho 15)) (bv_unsigned (rw rho 16)) eq_refl eq_refl B2) in A4.
  destruct A5 as [_ A5]. change (2 ^ 3) with 8 in A5.
  unfold rdZ. subst B L O C. repeat split; lia.
Qed.
End BaseZ.

Lemma rd_Hi : ltac2:(tb__ "0|0|
S2cS24S6aA1S76S0S20S4aS2eA1A1A2S23S6aS6dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rd_H17 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1Z11A2S14Z3fA1A3"). Proof. reflexivity. Qed.
Lemma rd_H10 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1ZaA2S14Z3A1A3"). Proof. reflexivity. Qed.
Lemma rd_H11 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1ZbA2S31A3"). Proof. reflexivity. Qed.
Lemma rd_H12 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1ZcA2S33A3"). Proof. reflexivity. Qed.
Lemma rd_Hnth : ltac2:(tb__ "0|0|
S2cS24S17A1S62S17S1fS4aS2eA1A1U2A3S23S17S1cS31S14Z0A1S33S22S12A1S1aA5A2A3"). Proof. reflexivity. Qed.
Lemma rd_next : ss_next (ax_S E_ecall) = 100%positive. Proof. reflexivity. Qed.

Section EcallFacts.
Variable rhoE : valuation.
Hypothesis HFE : ltac2:(tb__ "0|0|
S49ScSfVrhoE;A1S13S4aS2eA1A1A3").
Let Z0 := base_rd_Z rhoE HFE.

Lemma rd_Vbuf : ltac2:(tb__ "0|1|
S2cS47S2Q40M0S10VrhoE;S31A2A2S6S2G0SdVrhoE;PfA2A2S2G0SdVrhoE;P11A2A2A2A3").
Proof using Z0.
  pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). unfold HSE in Z3.
  pose proof (urange (rw rhoE 15)). pose proof (urange (rw rhoE 17)). pose proof (urange (rw rhoE 16)).
  unfold buf, add, vBb, vOb. apply U_add2; [reflexivity | reflexivity | lia].
Qed.

Lemma rd_Hcnt : ltac2:(tb__ "0|0|
S5S2Q40S10VrhoE;S11S4aS2eA1ZcA2A2A2S5aA2").
Proof using Z0. rewrite rd_H12. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). change (eval rhoE vC) with (rw rhoE 19). unfold MAX_RW_COUNT. lia. Qed.
Lemma rd_Hcnt_pos : ltac2:(tb__ "0|0|
S7Z0S2Q40S10VrhoE;S11S4aS2eA1ZcA2A2A2A2").
Proof using Z0. rewrite rd_H12. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). change (eval rhoE vC) with (rw rhoE 19). lia. Qed.
Lemma rd_Hov : ltac2:(tb__ "0|2|
S5S6S2Q40M0S10VrhoE;S11S4aS2eA1M1ZbA2A2A2S2G0S10VrhoE;S11G1ZcA2A2A2A2S5bA2").
Proof using Z0.
  rewrite rd_H11, rd_H12, rd_Vbuf. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
  change (eval rhoE vC) with (rw rhoE 19). pose proof (urange (rw rhoE 17)). unfold TASK_SIZE. lia.
Qed.
Lemma rd_Hbuf : ltac2:(tb__ "0|1|
S2cS47S2Q40M0S10VrhoE;S11S4aS2eA1ZbA2A2A2S6S2G0S10VrhoE;S31A2A2Z0A2A3").
Proof. rewrite rd_H11. lia. Qed.
Lemma rd_Hlo : soff rhoE (SLit 0) <= 0.
Proof. rewrite soff_lit_small; lia. Qed.
Lemma rd_Hhi : ltac2:(tb__ "0|0|
S5S6Z0S2Q40S10VrhoE;S11S4aS2eA1ZcA2A2A2A2S1dVrhoE;S33A2A2").
Proof using Z0.
  rewrite rd_H12. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). change (eval rhoE vC) with (rw rhoE 19).
  unfold vC. rewrite soff_var'; lia.
Qed.
Lemma rd_Hcells : Forall (fun c => soff rhoE (c_off c) + c_width c <= 0) ([] : list cell).
Proof. constructor. Qed.
Lemma rd_Hwoff : 0 = soff rhoE (SLit 0).
Proof. rewrite soff_lit_small; lia. Qed.
End EcallFacts.

Section LoopZr.
Variable lv : positive.
Hypothesis Hlv : ltac2:(tb__ "0|0|
S2bS63P64Vlv;A2S64Vlv;P8cA2A2").
Local Abbreviation res := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv).
Local Abbreviation lastb := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.lastb lv).

Section Vals.
Variable r : valuation.
Let B := bv_unsigned (rw r 15). Let L := bv_unsigned (rw r 16). Let O := bv_unsigned (rw r 17). Let N := bv_unsigned (rw r lv).
Hypothesis HZ : rdZ r.
Hypothesis HN : ltac2:(tb__ "0|0|
S2bS5Z1VN;A2S5S6VO;VN;A2VL;A2A2").

Lemma Vr_buf : ltac2:(tb__ "0|0|
S2cS47S2Q40S10Vr;S31A2A2S6VB;VO;A2A3").
Proof using HZ HN.
  unfold rdZ in HZ. pose proof (urange (rw r 15)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)).
  unfold buf, add, vBb, vOb. apply U_add2; [reflexivity | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma Vr_last : ltac2:(tb__ "0|0|
S2cS47S2Q40S10Vr;S3eVlv;A1A2A2SaS6S6VB;VO;A2VN;A2Z1A2A3").
Proof using HZ HN.
  pose proof Vr_buf as Vo. unfold rdZ in HZ. pose proof (urange (rw r 15)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)). pose proof (urange (rw r lv)).
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.lastb. unfold add at 1. unfold add at 1.
  replace (B + O + N - 1) with ((B + O + N) + (-1)) by lia.
  apply (U_addc r (SAlu ALU_ADD buf res) (-1) (B + O + N)); [ | subst B L O N; unfold HSE in HZ; lia | lia].
  apply U_add2; [exact Vo | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma Vr_BL : ltac2:(tb__ "0|0|
S2cS47S2Q40S10Vr;S66S45S46A2A2A2S6VB;VL;A2A3").
Proof using HZ HN.
  unfold rdZ in HZ. pose proof (urange (rw r 15)). pose proof (urange (rw r 16)).
  unfold add, vBb, vLb. apply U_add2; [reflexivity | reflexivity | subst B L O N; lia].
Qed.

Lemma F_Lr_intro : ltac2:(tb__ "0|3|
S47S47S2cS47S2Q40M0SdVr;P8cA2A2R2A3S2cS47S2G0SdVr;P8dA2A2R2A3S5VB;S8Z8M1R4A2A2S5S6S8G1R5A2G1A2S6VB;VL;A2A2S7R6R5A2S7R6S9Z2Z3dA2A2S5S8G1R7A2SaS6S6VB;VO;A2VN;A2Z1A2M2A2S5G2S6S8G1R8A2Z7A2A2S49ScSfVr;A1S35Vlv;A1A3F_;F_;F_;F_;F_;F_;F_;F_;Fl;Fc;").
Proof using HZ HN.
  intros c l Ec El H1 H2 H3 H4 H5 H6. unfold rdZ in HZ.
  pose proof (urange (rw r 15)). pose proof (urange (rw r 16)). pose proof (urange (rw r 17)).
  assert (Hc : bv_unsigned (rw r 140) < 2 ^ 61) by lia.
  assert (Eg8c : UU r (g8 cur) = 8 * c) by (unfold cur; rewrite (U_g8 r 140 Hc); lia).
  assert (Eg8l : UU r (g8 gl) = 8 * l) by (unfold gl; rewrite (U_g8 r 141 ltac:(lia)); lia).
  unfold F_L, F8of.
  constructor. { cbn [holds]. rewrite Eg8c. change (eval r vBb) with (rw r 15). lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 cur) 8 (8 * c) Eg8c) by lia. fold (add vBb vLb). rewrite Vr_BL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r cur) with (rw r 140). lia. }
  constructor. { cbn [holds]. change (eval r cur) with (rw r 140). change (eval r gl) with (rw r 141). lia. }
  constructor. { cbn [holds]. rewrite Eg8l. rewrite Vr_last. lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 gl) 7 (8 * l) Eg8l) by lia. rewrite Vr_last. lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r gl) with (rw r 141). lia. }
  constructor.
Qed.
End Vals.

Lemma Fpos_Z : ltac2:(tb__ "0|3|
SeS60R1A1S49ScSfR2A1S2fVlv;A1A3S2bS5Z1S2Q40M0SdR3Vlv;A2A2M1A2S2bS5S6S2G0SdR3P11A2A2G1A2S2G0SdR3P10A2A2M2A2S5G1G2A2A2A2F_;F_;Frho;").
Proof.
  intros rho HZ HF. unfold rdZ in HZ. pose proof (urange (rw rho 17)). pose proof (urange (rw rho lv)). pose proof (urange (rw rho 16)).
  have_fact A1 HF (SPUle (SLit 1) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv)). have_fact A2 HF (SPUle (add vOb (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv)) vLb).
  have_fact A3 HF (SPUle (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv) vLb).
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res, vOb, vLb, add in A1, A2, A3. rewrite (U_lit64 rho 1) in A1 by lia. cbn [eval] in A1, A3.
  assert (B1 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho lv) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar lv) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho lv)) eq_refl eq_refl B1) in A2.
  cbn [eval] in A2. lia.
Qed.

Lemma in_facts_Zr : ltac2:(tb__ "0|a|
SeS60R1A1S49ScSfR2A1S2fVlv;A1A3S49ScSfR3A1S25ScS3cS3aP8eM0S31A3S25ScS3cS39P8dM1S3eVlv;A1A3S28ScS1bS19S6bS65S3aA1S65S39A1A3A1S22ScA1A3A3A3A3S2Q40M2SdR4PfA2A2S47S2G2SdR5P11A2A2S47S2G2SdR6Vlv;A2A2S47S2G2SdR7G0A2A2S47S2G2SdR8G1A2A2S47S2bS2bS5S8Z8M3R2A2M4S6R5R4A2M5A2S5G5S6G4Z7M6A2A2A2S2bS7R2S9Z2Z3dA2M7A2S2bS2bS5S8G3R1A2M8SaS6G5R3A2Z1A2M9A2S5G9S6G8G6A2A2A2S2bS7R1G7A2S7R2R1A2A2A2A2A2Tl;Tg;TN;TO;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HP HF. pose proof HZ as HZ'. unfold rdZ in HZ'. destruct (Fpos_Z rho HZ HP) as (P1 & P2 & P3).
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  have_fact A1 HF (SPUle (g8 gs) buf). have_fact A2 HF (SPUle buf (add (g8 gs) (SLit 7))). have_fact A3 HF (SPUle gs (SLit (2 ^ 61 - 1))).
  have_fact A4 HF (SPUle (g8 gl) lastb). have_fact A5 HF (SPUle lastb (add (g8 gl) (SLit 7))). have_fact A6 HF (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A7 HF (SPNot (SPBranch BC_GEU (shp gs) (shp gl))).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A6 by lia.
  change (eval rho gs) with (rw rho 142) in A3. change (eval rho gl) with (rw rho 141) in A6.
  assert (Hg : bv_unsigned (rw rho 142) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (U_g8 rho 142 Hg) as Eg. pose proof (U_g8 rho 141 Hl) as El. unfold gs in A1, A2, A7. unfold gl in A4, A5, A7.
  rewrite Eg in A1. rewrite El in A4.
  pose proof (Vr_buf rho HZ (conj P1 P2)) as Vo. pose proof (Vr_last rho HZ (conj P1 P2)) as Vl.
  rewrite Vo in A1. rewrite Vo in A2. rewrite Vl in A4. rewrite Vl in A5.
  unfold add in A2, A5.
  pose proof (U_addc rho (g8 (SVar 142)) 7 _ Eg ltac:(lia) ltac:(lia)) as T1. rewrite T1 in A2.
  pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A5.
  cbn [holds branch_taken] in A7. unfold bv_ltu in A7.
  pose proof (U_shp rho 142 ltac:(lia)) as S1. pose proof (U_shp rho 141 ltac:(lia)) as S2.
  assert (Hgl : bv_unsigned (rw rho 142) < bv_unsigned (rw rho 141)).
  { destruct (Z.ltb_spec (UU rho (shp (SVar 142))) (UU rho (shp (SVar 141)))) as [Hlt|Hge];
      [rewrite S1, S2 in Hlt; lia | exfalso; apply A7; reflexivity]. }
  cbv zeta. repeat split; lia.
Qed.

Lemma bk_facts_Zr : ltac2:(tb__ "0|5|
SeS60R1A1S49ScSfR2A1S2fVlv;A1A3S49ScSfR3A1S25ScS35Vlv;A1S28ScS19S6cS67S37Z1M0A2S65S39A1A3S22ScA1A3A3A3S2Q40M1SdR4PfA2A2S47S2G1SdR5P10A2A2S47S2G1SdR6P11A2A2S47S2G1SdR7Vlv;A2A2S47S2G1SdR8P8cA2A2S47S2G1SdR9P8dA2A2S47S2bS5R6S8Z8M2R2A2A2S2bS7R2R1A2S2bS7R1S9Z2Z3dA2A2S2bS2bS5S8G2R1A2M3SaS6S6R6R4A2R3A2G0A2M4A2S5G4S6G3Z7A2A2A2S2dS2cS47S6R2G0A2R1A3A1A2A2A2A2Tl;Tc;TN;TO;TL;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HP HF. pose proof HZ as HZ'. unfold rdZ in HZ'. destruct (Fpos_Z rho HZ HP) as (P1 & P2 & P3).
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  apply Forall_app in HF as [HL HB].
  have_fact A1 HL (SPUle vBb (g8 cur)). have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). have_fact A4 HL (SPUlt cur gl).
  have_fact A5 HL (SPUle (g8 gl) lastb). have_fact A6 HL (SPUle lastb (add (g8 gl) (SLit 7))). have_fact A7 HL (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A8 HB (SPBranch BC_NE (shpk cur 1) (shp gl)).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A7 by lia.
  change (eval rho cur) with (rw rho 140) in A3, A4. change (eval rho gl) with (rw rho 141) in A4, A7.
  change (eval rho vBb) with (rw rho 15) in A1.
  assert (Hc : bv_unsigned (rw rho 140) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (U_g8 rho 140 Hc) as Ec. pose proof (U_g8 rho 141 Hl) as El. unfold cur in A1, A8. unfold gl in A5, A6, A8.
  rewrite Ec in A1. rewrite El in A5. pose proof (Vr_last rho HZ (conj P1 P2)) as Vl. rewrite Vl in A5. rewrite Vl in A6.
  unfold add in A6. pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A6.
  cbn [holds branch_taken] in A8. unfold bv_eqb in A8. apply negb_true_iff in A8. apply Z.eqb_neq in A8.
  pose proof (U_shp rho 141 ltac:(lia)) as S2. rewrite S2 in A8.
  unfold shpk, add in A8.
  rewrite (U_addc rho (SVar 140) (SHB + 1) (bv_unsigned (rw rho 140)) eq_refl) in A8 by (unfold SHB; lia).
  cbv zeta. repeat split; try lia.
Qed.
End LoopZr.

Lemma agree_sub_nil : ltac2:(tb__ "0|0|
S48SeS16R2R1S5fR1S22S29S48S15A2A1A2A3Frho;Fn;").
Proof. intros n rho. split; [intros i _; reflexivity|]. split; intros; reflexivity. Qed.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S48SeSeS21ScA1S16R4R3R2A3S2cS26S61ScS18R5A1R2A3S27A3S49ScSfR5A1M0R3A3S49ScG0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Lemma FR_Z : ltac2:(tb__ "0|1|
S48SeS49ScSfR1A1S34R2A1A3S2bS60R2A1S5S2Q40M0SdR2R3A2A2S2G0SdR2P13A2A2A2A2F_;Frho;Flv;").
Proof.
  intros lv rho HF. unfold FR in HF. apply Forall_app in HF as [H1 H2]. split; [exact (base_rd_Z rho H2)|].
  have_fact A H1 (SPUle (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv) vC). exact A.
Qed.

Ltac split_mid3 HF HX HT := cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Section GlueR.
Variables (bc : list cell) (lv : positive).
Hypothesis Hlv : ltac2:(tb__ "0|0|
S2bS63P64Vlv;A2S64Vlv;P8cA2A2").
Variable rho : valuation.

Lemma Fpos_below200 : ltac2:(tb__ "0|0|
S2cS26S61ScS18Pc8A1S2fVlv;A1A3S27A3").
Proof using Hlv.
  unfold Fpos, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res, vOb, vLb, add. cbn. destruct Hlv as [H1 H2].
  rewrite !(proj2 (Pos.ltb_lt lv 200)) by lia. reflexivity.
Qed.

Lemma glue_pos : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S13S4aS43Vbc;Vlv;A2A1A1A3S49ScSfS5fVrho;S22S29S48S15A2A1A2A1S2fVlv;A1A3F_;").
Proof using Hlv.
  intros HF. unfold E_pos in HF. split_mid3 HF HX HT. destruct (FR_Z lv rho HT) as [HZ Hle]. pose proof HZ as HZ'. unfold rdZ in HZ'.
  pose proof (urange (rw rho lv)) as Rl. pose proof (urange (rw rho 17)) as R17.
  have_fact A1 HX (SPNot (SPBranch BC_GE (SLit 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv))).
  cbn [holds branch_taken] in A1. unfold bv_lts in A1.
  assert (Hpos : 1 <= bv_unsigned (rw rho lv)).
  { destruct (Z.ltb_spec (bv_signed (eval rho (SLit 0))) (bv_signed (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv)))) as [Hlt|Hge]; [| exfalso; apply A1; reflexivity].
    rewrite !bv_signed_U in Hlt. change (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv)) with (rw rho lv) in Hlt.
    rewrite (U_lit64 rho 0) in Hlt by lia.
    destruct (Zsigned_spec 0) as [[_ E0]|[X0 _]]; [rewrite E0 in Hlt | lia].
    destruct (Zsigned_spec (bv_unsigned (rw rho lv))) as [[_ E]|[X _]]; [rewrite E in Hlt; lia | lia]. }
  apply (Forall_holds_agree 200 rho); [apply agree_sub_nil | exact Fpos_below200 |].
  unfold Fpos. constructor.
  { cbn [holds]. rewrite (U_lit64 rho 1) by lia. change (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv)) with (rw rho lv). lia. }
  constructor.
  { cbn [holds]. unfold add, vOb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res, vLb.
    rewrite (U_add2 rho (SVar 17) (SVar lv) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho lv)) eq_refl eq_refl) by lia.
    cbn [eval]. lia. }
  constructor. { cbn [holds]. change (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.res lv)) with (rw rho lv). change (eval rho vLb) with (rw rho 16). lia. }
  constructor.
Qed.

Lemma glue_L_in : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S13S4aS42Vbc;Vlv;A2A1A1A3S49ScSfS5fVrho;S40A2A1S35Vlv;A1A3F_;").
Proof using Hlv.
  intros HF. unfold E_L_in in HF. split_mid3 HF HX HT. destruct (FR_Z lv rho HT) as [HZ Hle].
  apply Forall_app in HX as [HA HX]. apply Forall_app in HX as [HB HX]. apply Forall_app in HX as [HC HP].
  assert (HX1 : Forall (holds rho) (F8of gs 142 buf ++ F8of gl 141 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.lastb lv) ++ [SPNot (SPBranch BC_GEU (shp gs) (shp gl))])).
  { apply Forall_app. split; [exact HA|]. apply Forall_app. split; [exact HB | exact HC]. }
  destruct (Fpos_Z lv Hlv rho HZ HP) as (P1 & P2 & P3).
  destruct (in_facts_Zr lv Hlv rho HZ HP HX1) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  pose proof HZ as HZ'. unfold rdZ in HZ'. unfold HSE in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141. pose proof (urange (rw rho 17)) as R17.
  set (rho' := rho_sub rho s_L_in).
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity. assert (E16 : rw rho' 16 = rw rho 16) by reflexivity.
  assert (E17 : rw rho' 17 = rw rho 17) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E10 : rw rho' 10 = rw rho 10) by reflexivity. assert (E24 : rw rho' 24 = rw rho 24) by reflexivity.
  assert (Elv : rw rho' lv = rw rho lv).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_in]. destruct Hlv as [H1 H2].
    replace (Pos.eqb lv 140) with false by (symmetry; apply Pos.eqb_neq; lia). reflexivity. }
  assert (HZr : rdZ rho') by (unfold rdZ; rewrite E15, E16, E17, E19, E10, E24; exact HZ').
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D.
  apply (F_Lr_intro lv rho' HZr ltac:(rewrite Elv, E17, E16; lia) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E15, ?E16, ?E17, ?Elv; lia.
Qed.

Lemma glue_L_bk : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S13S4aS41Vbc;Vlv;A2A1A1A3S49ScSfS5fVrho;S3fA2A1S35Vlv;A1A3F_;").
Proof using Hlv.
  intros HF. unfold E_L_bk in HF. split_mid3 HF HX HT. destruct (FR_Z lv rho HT) as [HZ Hle].
  apply Forall_app in HX as [HA HX]. apply Forall_app in HX as [HB HP].
  assert (HX1 : Forall (holds rho) (F_L lv ++ [SPBranch BC_NE (shpk cur 1) (shp gl)])).
  { apply Forall_app. split; [exact HA | exact HB]. }
  destruct (Fpos_Z lv Hlv rho HZ HP) as (P1 & P2 & P3).
  destruct (bk_facts_Zr lv Hlv rho HZ HP HX1) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  pose proof HZ as HZ'. unfold rdZ in HZ'. unfold HSE in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141. pose proof (urange (rw rho 17)) as R17.
  set (rho' := rho_sub rho s_L_bk).
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity. assert (E16 : rw rho' 16 = rw rho 16) by reflexivity.
  assert (E17 : rw rho' 17 = rw rho 17) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E10 : rw rho' 10 = rw rho 10) by reflexivity. assert (E24 : rw rho' 24 = rw rho 24) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  assert (Elv : rw rho' lv = rw rho lv).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_bk]. destruct Hlv as [H1 H2].
    replace (Pos.eqb lv 140) with false by (symmetry; apply Pos.eqb_neq; lia). reflexivity. }
  assert (HZr : rdZ rho') by (unfold rdZ; rewrite E15, E16, E17, E19, E10, E24; exact HZ').
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  apply (F_Lr_intro lv rho' HZr ltac:(rewrite Elv, E17, E16; lia) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E15, ?E16, ?E17, ?Elv, ?E141; try lia.
Qed.

Lemma meas_L_in : ltac2:(tb__ "0|0|
S2cS3Q40A1S10S5fVrho;S40A2S37A2S10Vrho;S3aA2A3").
Proof. reflexivity. Qed.
Lemma meas_L_bk : ltac2:(tb__ "0|0|
S2cS3Q40A1S10S5fVrho;S3fA2S37A2S10Vrho;S66S37S14Z1A1A2A2A3").
Proof. reflexivity. Qed.
End GlueR.

Lemma FposFR_of_Ereg : ltac2:(tb__ "0|0|
S21S12A1S48SeS49ScSfR1A1S13S4aS3bR3R2A2A1A1A3S49ScSfR2A1S25ScS2fR3A1S34R3A1A3A3F_;Fr;Flv;Fbc;").
Proof. intros bc lv r HF. cbn [ax_S ss_facts E_reg mid_state mkA] in HF. exact HF. Qed.
Lemma FposFR_below190 : ltac2:(tb__ "0|3|
S2bS2cS26S61ScS18PbeA1M0S25ScS2fP64M1A1S34G1A1A3A3S27A3S2cS26S61ScG0S25ScS2fP65M2A1S34G2A1A3A3S27A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma next_Ereg : ltac2:(tb__ "0|1|
S21S12A1S48S2bS63P65S1eS4aS3bR2R1A2A1A1M0A2S63P66G0A2A2Flv;Fbc;").
Proof. intros. cbn. split; cbv; congruence. Qed.
Lemma Hlv100 : (100 <= 100)%positive /\ (100 < 140)%positive. Proof. split; cbv; congruence. Qed.
Lemma Hlv101 : (100 <= 101)%positive /\ (101 < 140)%positive. Proof. split; cbv; congruence. Qed.

Lemma LQA_unG' : ltac2:(tb__ "0|0|
S4fS48S48SeSeS21S3Q40A1A1S21S4bA1S5eS4cS0S77SeS16R8R6R1A3Lr;R8A2R6R4R3R2R1A7S4cS0R9R8R6R4R3R2A7F_;Fw;Fposts;Ftp;Frho1;Frho;Fm;Fn;FJ;").
Proof. intros J n m rho rho1 tp posts w (L & rho'' & Hin & _ & Hsm & [Hag Hk]). exists L, rho''. auto. Qed.

Section Seg3Keep.
Variable ok : assn.
Variable J1x : jpredA.
Hypothesis Hok1 : ltac2:(tb__ "0|0|
S4eS0Vok;VJ1x;A3").
Hypothesis Hst1 : stableA segs 101 J1x.

Lemma seg3_keep : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P64M1A2A2S2G0SdR2P13A2A2A2S5dS0Vok;S4dS0VJ1x;S6eS2eA1R3R2A5S4cS0VJ1x;P65R3R2S30S22S12A1G1A2A6A4F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 101 rho1 r) J1x).
  assert (HstG : stableA segs 101 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  assert (HokG : ok_frameA segs ok J3) by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  destruct ids_rd as (_ & _ & _ & I1 & I2 & I3).
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 101 T_rd_k rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  apply (cfg_soundA segs FUELR cutpcs_rd 101 cuts_k exits_k J3 ok (LQA segs J1x 101 rho1 tp (Posts_rd [] 100)) tp HokG HstG check_k);
    [| left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply exit_postA. in_nth 0.
  - apply (exit_reenterA segs ok _ 101 cuts_k _ (E_pos [] 100) (T_pos_0 [] 100) (Fpos 100) [] tp);
      [in_nth 1 | exact ent_pos_k | exact I1 | exact HstG | exact (proj1 Fpos_below) | intros r tp' tr md _ HF; exact (glue_pos [] 100 Hlv100 r HF)].
  - apply (call_exitA ok J1x 101 rho1 tp (E_reg [] 100) Pre_rip_lo s_reg_k R_reg_k Posts_rip (Fpos 100 ++ FR 100) Hst1 fr_reg_k cc_reg_k
             (proj1 (next_Ereg [] 100)) (FposFR_of_Ereg [] 100) (proj1 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_Tr)) | or_intror F => match F with end end)
             cuts_k _ Hok1).
    + intros ok' Jq rho2 tp2 Ho Hs. exact (region_sum_lo ok' Jq rho2 tp2 Ho Hs).
    + intros L [<-|[]]. in_nth 2.
  - apply (exit_reenterA segs ok _ 101 cuts_k _ (E_L_in [] 100) (CL_0 [] 100) (F_L 100) s_L_in tp);
      [in_nth 3 | exact ent_L_in_k | exact I2 | exact HstG | exact (proj1 FL_below) | intros r tp' tr md _ HF; exact (glue_L_in [] 100 Hlv100 r HF)].
  - apply (exit_reenterA segs ok _ 101 cuts_k _ (E_L_bk [] 100) (CL_0 [] 100) (F_L 100) s_L_bk tp);
      [in_nth 3 | exact ent_L_bk_k | exact I3 | exact HstG | exact (proj1 FL_below) | intros r tp' tr md _ HF; exact (glue_L_bk [] 100 Hlv100 r HF)].
Qed.
End Seg3Keep.

Section Seg3KeepEx.
Variable J1x : jpredA.
Hypothesis Hst1 : stableA segs 101 J1x.

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma seg3_keep_ex : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P64M1A2A2S2G0SdR2P13A2A2A2S5cS0S4dS0VJ1x;S6eS2eA1R3R2A5S4cS0VJ1x;P65R3R2S30S22S12A1G1A2A6A3F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 101 rho1 r) J1x).
  assert (HstG : stableA segs 101 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  destruct ids_rd as (_ & _ & _ & I1 & I2 & I3).
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 101 T_rd_k rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  change T_rd_k with (vna_state (mkVNA T_rd_k 200 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELR cutpcs_rd 101 vcuts_k vexits_k J3 (LQA segs J1x 101 rho1 tp (Posts_rd [] 100)) tp HstG);
    [ | exact echeck_k | | left; reflexivity].
  { intros m Hm. unfold vcuts_k, vcuts_rd in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply (eexit_post_IA0 segs J1x 101 rho1 vcuts_k (Posts_rd [] 100) (mkVNA (P_rd [] 100) 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply (eexit_reenter_IA segs _ 101 vcuts_k _ (mkVNA (E_pos [] 100) 150 (SLit 0)) (mkVNA (T_pos [] 100) 149 (SLit 0)) (Fpos 100) (T_pos_0 [] 100) [] tp);
      [in_nth 1 | reflexivity | exact ent_pos_k | exact I1 | exact HstG | exact (proj1 Fpos_below)
      | intros r tp' tr md _ HF; split; [exact (glue_pos [] 100 Hlv100 r HF) | right; split; [cbn; lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (call_exitA_ex J1x 101 rho1 tp (E_reg [] 100) Pre_rip_lo s_reg_k R_reg_k Posts_rip (Fpos 100 ++ FR 100) Hst1 fr_reg_k cc_reg_k
             (proj1 (next_Ereg [] 100)) (FposFR_of_Ereg [] 100) (proj1 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_Tr)) | or_intror F => match F with end end)
             vcuts_k _ (mkVNA (E_reg [] 100) 80 (SLit (2 ^ 61))) eq_refl).
    + intros Jq rho2 tp2 Hs. exact (region_sum_lo_ex Jq rho2 tp2 Hs).
    + intros L [<-|[]]. exists (mkVNA (Tr1 [] 100 s_reg_k R_reg_k) 79 (SLit (2 ^ 61))). split; [in_nth 2|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ 101 vcuts_k _ (mkVNA (E_L_in [] 100) 101 gs) (mkVNA (CL [] 100) 100 cur) (F_L 100) (CL_0 [] 100) s_L_in tp);
      [in_nth 3 | reflexivity | exact ent_L_in_k | exact I2 | exact HstG | exact (proj1 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_in [] 100 Hlv100 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ 101 vcuts_k _ (mkVNA (E_L_bk [] 100) 101 (add cur (SLit 1))) (mkVNA (CL [] 100) 100 cur) (F_L 100) (CL_0 [] 100) s_L_bk tp);
      [in_nth 3 | reflexivity | exact ent_L_bk_k | exact I3 | exact HstG | exact (proj1 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_bk [] 100 Hlv100 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.
End Seg3KeepEx.

Section ReadKeep.
Variables (J0 J1 : jpredA) (p : list byte) (data : list byte) (offZ : valuation -> Z).
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hst1 : stableA segs 101 J1.
Hypothesis Hoff : ltac2:(tb__ "0|1|
SeS2bS5Z0VoffZ;R1A1M0A2S7G0S9Z2Z40A2A2A2Fr;").
Hypothesis HJfd : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S21S53A1S52VJ0;R4R3R2R1A4S2bS2cS24S54A1S55S56R2A1S4G0Z3A2A2S23S54S57Vp;S4G0VoffZ;R5A1A2A2A2A3S2cS24S21S3Q8A1A1M1A1S69S58R2A1Vp;A2S23G1Vdata;A2A3A2F_;Fmd;Ftr;Ft;Fr;").

Hypothesis HK : ltac2:(tb__ "0|1|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4VJ1;S72S2eR5Vdata;VoffZ;R5A1M0A4R4R3S70S2eR5Vp;Vdata;G0R2A6A4F_;Fmd;Ftr;Ft;Fr;").

Lemma len_le : ltac2:(tb__ "0|2|
SeS49ScSfR1A1S13S4aS2eA1A1A3S5S2Q40M0SdS72S2eR2Vdata;VoffZ;R2A1A4M1P64A2A2S2G0SdG1P13A2A2A2F_;Fr;").
Proof.
  intros r HF. unfold rkA_rho'. rewrite rd_next. rewrite rho_set_rw_at, rho_set_rw_other by (cbv; congruence).
  pose proof (rbA_bs_len E_ecall r data (offZ r) (Hoff r)) as Hl. rewrite rd_H12 in Hl.
  change (eval r vC) with (rw r 19) in Hl. pose proof (urange (rw r 19)).
  rewrite len_word_unsigned by (unfold two_pow_64; lia). exact Hl.
Qed.

Theorem read_keep_sum : ltac2:(tb__ "0|0|
S5eOF_;SeS21S3Q40A1A1S4eS0R3VJ0;A3S68S0R4VJ0;A3S4eS0R5VJ1;A3S5dS0R6S4dS0VJ0;S32R5R4A5S4cS0VJ1;S51R5R4S30S22S12A1P64A2A6A4F_;F_;F_;Ftp;Frho;Fok;").
Proof.
  intros ok rho tp Hok0 Hokp0 Hok1.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 101 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  assert (HokG0 : ok_frameA segs ok J0') by (intros r t tr ms md msv' [_ HJ]; eapply Hok0; eauto).
  assert (HokpG0 : ok_pframeA segs ok J0') by (intros r t tr ms md x8 [_ HJ]; eapply Hokp0; eauto).
  assert (HokG1 : ok_frameA segs ok J1') by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [rd_ecall] NF [Pre_rd] [E_ecall] J0' ok (LQA segs J1 NF rho tp (Posts_rd [] 100)) tp HokG0 HstG0 check_rd1);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  apply triple_factsA. intros HFE.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply triple_seq with (R := SPA segs J1' (A_after_fresh E_ecall) (rkA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply triple1_triple.
    apply (triple1_read_keepA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE)
             ok J0' J1' HokG0 HokpG0 HstG0 HstG1).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rkA_rho'. apply agree_below_set_rw. rewrite rd_next. apply Pos.le_refl.
  - eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg3_keep ok J1' HokG1 HstG1); exact (len_le rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 101 rho _ tp _ w Hw).
Qed.

Theorem read_keep_sum_ex : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S5cS0S4dS0VJ0;S32R2R1A5S4cS0VJ1;S51R2R1S30S22S12A1P64A2A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 101 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_rd with (vna_state (mkVNA Pre_rd 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [rd_ecall] NF [mkVNA Pre_rd 1 (SLit 0)] [mkVNA E_ecall 0 (SLit 0)] J0'
           (LQA segs J1 NF rho tp (Posts_rd [] 100)) tp HstG0);
    [intros n [<-|[]]; cbv; congruence | exact echeck_rd1 | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  apply etriple_factsA. intros HFE.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply etriple_seq with (R := SPA segs J1' (A_after_fresh E_ecall) (rkA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply (etriple_read_keepA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE)
             J0' J1' HstG0 HstG1).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rkA_rho'. apply agree_below_set_rw. rewrite rd_next. apply Pos.le_refl.
  - eapply etriple_conseq; [intros w Hw; exact Hw | | apply (seg3_keep_ex J1' HstG1); exact (len_le rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 101 rho _ tp _ w Hw).
Qed.
End ReadKeep.

Section Seg3Hdr.
Variable ok : assn.
Variable J1x : jpredA.
Hypothesis Hok1 : ltac2:(tb__ "0|0|
S4eS0Vok;VJ1x;A3").
Hypothesis Hst1 : stableA segs 102 J1x.

Lemma seg3_hdr : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P65M1A2A2S2G0SdR2P13A2A2A2S5dS0Vok;S4dS0VJ1x;S6fS2eU2S31S14Z0A1S33A5R3R2A5S4cS0VJ1x;P66R3R2S30S38G1A2A6A4F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 102 rho1 r) J1x).
  assert (HstG : stableA segs 102 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  assert (HokG : ok_frameA segs ok J3) by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  destruct ids_rd as (I1 & I2 & I3 & _).
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 102 T_rd_h rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  apply (cfg_soundA segs FUELR cutpcs_rd 102 cuts_h exits_h J3 ok (LQA segs J1x 102 rho1 tp (Posts_rd hc 101)) tp HokG HstG check_h);
    [| left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply exit_postA. in_nth 0.
  - apply (exit_reenterA segs ok _ 102 cuts_h _ (E_pos hc 101) (T_pos_0 hc 101) (Fpos 101) [] tp);
      [in_nth 1 | exact ent_pos_h | exact I1 | exact HstG | exact (proj2 Fpos_below) | intros r tp' tr md _ HF; exact (glue_pos hc 101 Hlv101 r HF)].
  - apply (call_exitA ok J1x 102 rho1 tp (E_reg hc 101) Pre_rip_lo s_reg_h R_reg_h Posts_rip (Fpos 101 ++ FR 101) Hst1 fr_reg_h cc_reg_h
             (proj2 (next_Ereg hc 101)) (FposFR_of_Ereg hc 101) (proj2 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_Tr)) | or_intror F => match F with end end)
             cuts_h _ Hok1).
    + intros ok' Jq rho2 tp2 Ho Hs. exact (region_sum_lo ok' Jq rho2 tp2 Ho Hs).
    + intros L [<-|[]]. in_nth 2.
  - apply (exit_reenterA segs ok _ 102 cuts_h _ (E_L_in hc 101) (CL_0 hc 101) (F_L 101) s_L_in tp);
      [in_nth 3 | exact ent_L_in_h | exact I2 | exact HstG | exact (proj2 FL_below) | intros r tp' tr md _ HF; exact (glue_L_in hc 101 Hlv101 r HF)].
  - apply (exit_reenterA segs ok _ 102 cuts_h _ (E_L_bk hc 101) (CL_0 hc 101) (F_L 101) s_L_bk tp);
      [in_nth 3 | exact ent_L_bk_h | exact I3 | exact HstG | exact (proj2 FL_below) | intros r tp' tr md _ HF; exact (glue_L_bk hc 101 Hlv101 r HF)].
Qed.
End Seg3Hdr.

Section Seg3HdrEx.
Variable J1x : jpredA.
Hypothesis Hst1 : stableA segs 102 J1x.

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma seg3_hdr_ex : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P65M1A2A2S2G0SdR2P13A2A2A2S5cS0S4dS0VJ1x;S6fS2eU2S31S14Z0A1S33A5R3R2A5S4cS0VJ1x;P66R3R2S30S38G1A2A6A3F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 102 rho1 r) J1x).
  assert (HstG : stableA segs 102 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  destruct ids_rd as (I1 & I2 & I3 & _).
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 102 T_rd_h rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  change T_rd_h with (vna_state (mkVNA T_rd_h 200 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELR cutpcs_rd 102 vcuts_h vexits_h J3 (LQA segs J1x 102 rho1 tp (Posts_rd hc 101)) tp HstG);
    [ | exact echeck_h | | left; reflexivity].
  { intros m Hm. unfold vcuts_h, vcuts_rd in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply (eexit_post_IA0 segs J1x 102 rho1 vcuts_h (Posts_rd hc 101) (mkVNA (P_rd hc 101) 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply (eexit_reenter_IA segs _ 102 vcuts_h _ (mkVNA (E_pos hc 101) 150 (SLit 0)) (mkVNA (T_pos hc 101) 149 (SLit 0)) (Fpos 101) (T_pos_0 hc 101) [] tp);
      [in_nth 1 | reflexivity | exact ent_pos_h | exact I1 | exact HstG | exact (proj2 Fpos_below)
      | intros r tp' tr md _ HF; split; [exact (glue_pos hc 101 Hlv101 r HF) | right; split; [cbn; lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (call_exitA_ex J1x 102 rho1 tp (E_reg hc 101) Pre_rip_lo s_reg_h R_reg_h Posts_rip (Fpos 101 ++ FR 101) Hst1 fr_reg_h cc_reg_h
             (proj2 (next_Ereg hc 101)) (FposFR_of_Ereg hc 101) (proj2 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_Tr)) | or_intror F => match F with end end)
             vcuts_h _ (mkVNA (E_reg hc 101) 80 (SLit (2 ^ 61))) eq_refl).
    + intros Jq rho2 tp2 Hs. exact (region_sum_lo_ex Jq rho2 tp2 Hs).
    + intros L [<-|[]]. exists (mkVNA (Tr1 hc 101 s_reg_h R_reg_h) 79 (SLit (2 ^ 61))). split; [in_nth 2|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ 102 vcuts_h _ (mkVNA (E_L_in hc 101) 101 gs) (mkVNA (CL hc 101) 100 cur) (F_L 101) (CL_0 hc 101) s_L_in tp);
      [in_nth 3 | reflexivity | exact ent_L_in_h | exact I2 | exact HstG | exact (proj2 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_in hc 101 Hlv101 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ 102 vcuts_h _ (mkVNA (E_L_bk hc 101) 101 (add cur (SLit 1))) (mkVNA (CL hc 101) 100 cur) (F_L 101) (CL_0 hc 101) s_L_bk tp);
      [in_nth 3 | reflexivity | exact ent_L_bk_h | exact I3 | exact HstG | exact (proj2 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_bk hc 101 Hlv101 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.
End Seg3HdrEx.

Section ReadHdr.
Variables (J0 J1 : jpredA) (p : list byte) (data : list byte) (offZ : valuation -> Z).
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hst1 : stableA segs 102 J1.
Hypothesis Hoff : ltac2:(tb__ "0|1|
SeS2bS5Z0VoffZ;R1A1M0A2S7G0S9Z2Z40A2A2A2Fr;").
Hypothesis HJfd : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S21S53A1S52VJ0;R4R3R2R1A4S2bS2cS24S54A1S55S56R2A1S4G0Z3A2A2S23S54S57Vp;S4G0VoffZ;R5A1A2A2A2A3S2cS24S21S3Q8A1A1M1A1S69S58R2A1Vp;A2S23G1Vdata;A2A3A2F_;Fmd;Ftr;Ft;Fr;").

Hypothesis HK : ltac2:(tb__ "0|1|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4VJ1;S71S2eR5Vdata;VoffZ;R5A1M0A4R4R3S70S2eR5Vp;Vdata;G0R2A6A4F_;Fmd;Ftr;Ft;Fr;").
Hypothesis H4 : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4S74U4S2aS3Q8A1S73S2eR5Vdata;VoffZ;R5A1A4A2A2F_;Fmd;Ftr;Ft;Fr;").

Lemma len_le_h : ltac2:(tb__ "0|2|
SeS49ScSfR1A1S13S4aS2eA1A1A3S5S2Q40M0SdS71S2eR2Vdata;VoffZ;R2A1A4M1P65A2A2S2G0SdG1P13A2A2A2F_;Fr;").
Proof.
  intros r HF. unfold rhA_rho'. rewrite rd_next. cbn [Pos.succ].
  rewrite rho_set_rw_at. rewrite !rho_set_rw_other by (cbv; congruence).
  pose proof (rbA_bs_len E_ecall r data (offZ r) (Hoff r)) as Hl. rewrite rd_H12 in Hl.
  change (eval r vC) with (rw r 19) in Hl. pose proof (urange (rw r 19)).
  rewrite len_word_unsigned by (unfold two_pow_64; lia). exact Hl.
Qed.

Theorem read_hdr_sum : ltac2:(tb__ "0|0|
S5eOF_;SeS21S3Q40A1A1S4eS0R3VJ0;A3S68S0R4VJ0;A3S4eS0R5VJ1;A3S5dS0R6S4dS0VJ0;S32R5R4A5S4cS0VJ1;S51R5R4S30S38P65A2A6A4F_;F_;F_;Ftp;Frho;Fok;").
Proof.
  intros ok rho tp Hok0 Hokp0 Hok1.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 102 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  assert (HokG0 : ok_frameA segs ok J0') by (intros r t tr ms md msv' [_ HJ]; eapply Hok0; eauto).
  assert (HokpG0 : ok_pframeA segs ok J0') by (intros r t tr ms md x8 [_ HJ]; eapply Hokp0; eauto).
  assert (HokG1 : ok_frameA segs ok J1') by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [rd_ecall] NF [Pre_rd] [E_ecall] J0' ok (LQA segs J1 NF rho tp (Posts_rd hc 101)) tp HokG0 HstG0 check_rd1);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  apply triple_factsA. intros HFE.
  eapply triple_conseq; [intros w Hw; exact (conj (H4 rhoE tp _ _ (proj2 (proj2 Hw))) Hw) | intros w Hw; right; exact Hw |].
  apply triple_pure. intros H4E.
  eapply triple_seq with (R := SPA segs J1' (A_after_hdr E_ecall 2 buf (SLit 0) vC) (rhA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply triple1_triple.
    apply (triple1_read_hdrA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE) eq_refl (rd_Hwoff rhoE)
             ok J0' J1' HokG0 HokpG0 HstG0 HstG1 H4E).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rhA_rho'. rewrite rd_next.
      eapply agree_below_trans; [apply agree_below_set_rw; apply Pos.le_refl | apply agree_below_set_rw; cbv; congruence].
  - eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg3_hdr ok J1' HokG1 HstG1); exact (len_le_h rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 102 rho _ tp _ w Hw).
Qed.

Theorem read_hdr_sum_ex : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S5cS0S4dS0VJ0;S32R2R1A5S4cS0VJ1;S51R2R1S30S38P65A2A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 102 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_rd with (vna_state (mkVNA Pre_rd 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [rd_ecall] NF [mkVNA Pre_rd 1 (SLit 0)] [mkVNA E_ecall 0 (SLit 0)] J0'
           (LQA segs J1 NF rho tp (Posts_rd hc 101)) tp HstG0);
    [intros n [<-|[]]; cbv; congruence | exact echeck_rd1 | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  apply etriple_factsA. intros HFE.
  eapply etriple_conseq; [intros w Hw; exact (conj (H4 rhoE tp _ _ (proj2 (proj2 Hw))) Hw) | intros w Hw; right; exact Hw |].
  apply etriple_pure. intros H4E.
  eapply etriple_seq with (R := SPA segs J1' (A_after_hdr E_ecall 2 buf (SLit 0) vC) (rhA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply (etriple_read_hdrA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE) eq_refl (rd_Hwoff rhoE)
             J0' J1' HstG0 HstG1 H4E).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rhA_rho'. rewrite rd_next.
      eapply agree_below_trans; [apply agree_below_set_rw; apply Pos.le_refl | apply agree_below_set_rw; cbv; congruence].
  - eapply etriple_conseq; [intros w Hw; exact Hw | | apply (seg3_hdr_ex J1' HstG1); exact (len_le_h rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 102 rho _ tp _ w Hw).
Qed.
End ReadHdr.

Section ReadDir.
Variables (J0 J1 : jpredA).
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hst1 : stableA segs NF J1.
Hypothesis HJfd : ltac2:(tb__ "0|1|
SeS21S3Q40M0A1A1S21S53A1S52VJ0;R4R3R2R1A4S2cS24S54A1S55S56R2A1S4G0Z3A2A2S23S54S59A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HK : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4VJ1;R5R4R3R2A4F_;Fmd;Ftr;Ft;Fr;").

Lemma seg3_dir : ltac2:(tb__ "0|0|
S5eOF_;S4fSeS21S3Q40A1A1S4eS0R4R3A3S50S0S51R4A3S5dS0R6S4dS0R5S3dR4R3A5S4cS0R5S51R4R3S36A6A4F_;F_;Ftp;Frho1;FJ1x;Fok;").
Proof.
  intros ok J1x rho1 tp Hok Hst.
  set (J3 := withGA (fun r => agree_below NF rho1 r) J1x).
  assert (HstG : stableA segs NF J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok J3) by (intros r t tr ms md msv' [_ HJ]; eapply Hok; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J1x NF T_rd_d rho1 tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [] NF [T_rd_d] [P_rd_d] J3 ok (LQA segs J1x NF rho1 tp Posts_rd_d) tp HokG HstG check_d); [| left; reflexivity].
  intros E rhoE [<-|[]]. apply exit_postA. in_nth 0.
Qed.

Lemma seg3_dir_ex : ltac2:(tb__ "0|0|
S4fSeS21S3Q40A1A1S50S0S51R3A3S5cS0S4dS0R4S3dR3R2A5S4cS0R4S51R3R2S36A6A3F_;Ftp;Frho1;FJ1x;").
Proof.
  intros J1x rho1 tp Hst.
  set (J3 := withGA (fun r => agree_below NF rho1 r) J1x).
  assert (HstG : stableA segs NF J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J1x NF T_rd_d rho1 tp w Hw) | intros w Hw; exact Hw |].
  change T_rd_d with (vna_state (mkVNA T_rd_d 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [] NF [mkVNA T_rd_d 1 (SLit 0)] [mkVNA P_rd_d 0 (SLit 0)] J3 (LQA segs J1x NF rho1 tp Posts_rd_d) tp HstG);
    [intros n [<-|[]]; cbv; congruence | exact echeck_d | | left; reflexivity].
  intros E rhoE [<-|[]]. apply (eexit_postA segs J1x NF rho1 [mkVNA T_rd_d 1 (SLit 0)] Posts_rd_d (mkVNA P_rd_d 0 (SLit 0))). in_nth 0.
Qed.

Theorem read_dir_sum : ltac2:(tb__ "0|0|
S5eOF_;SeS21S3Q40A1A1S4eS0R3VJ0;A3S68S0R4VJ0;A3S4eS0R5VJ1;A3S5dS0R6S4dS0VJ0;S32R5R4A5S4cS0VJ1;S51R5R4S36A6A4F_;F_;F_;Ftp;Frho;Fok;").
Proof.
  intros ok rho tp Hok0 Hokp0 Hok1.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs NF J1').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  assert (HokG0 : ok_frameA segs ok J0') by (intros r t tr ms md msv' [_ HJ]; eapply Hok0; eauto).
  assert (HokpG0 : ok_pframeA segs ok J0') by (intros r t tr ms md x8 [_ HJ]; eapply Hokp0; eauto).
  assert (HokG1 : ok_frameA segs ok J1') by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [rd_ecall] NF [Pre_rd] [E_ecall] J0' ok (LQA segs J1 NF rho tp Posts_rd_d) tp HokG0 HstG0 check_rd1);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  apply triple_factsA. intros HFE.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply triple_seq with (R := SPA segs J1' (dirA' E_ecall) rhoE tp).
  - apply triple1_triple.
    apply (triple1_read_dirA segs E_ecall rhoE tp rd_Hi rd_H17 rd_H10 (rd_Hov rhoE HFE)
             ok J0' J1' HokG0 HokpG0 HstG0).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [exact Hag | exact (HK rhoE tp tr md HJ)].
  - eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg3_dir ok J1' rhoE tp HokG1 HstG1)].
    intros w Hw. exact (LQA_unG' J1 NF NF rho _ tp _ w Hw).
Qed.

Theorem read_dir_sum_ex : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S5cS0S4dS0VJ0;S32R2R1A5S4cS0VJ1;S51R2R1S36A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs NF J1').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_rd with (vna_state (mkVNA Pre_rd 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [rd_ecall] NF [mkVNA Pre_rd 1 (SLit 0)] [mkVNA E_ecall 0 (SLit 0)] J0'
           (LQA segs J1 NF rho tp Posts_rd_d) tp HstG0);
    [intros n [<-|[]]; cbv; congruence | exact echeck_rd1 | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  apply etriple_factsA. intros HFE.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply etriple_seq with (R := SPA segs J1' (dirA' E_ecall) rhoE tp).
  - apply (etriple_read_dirA segs E_ecall rhoE tp rd_Hi rd_H17 rd_H10 (rd_Hov rhoE HFE)
             J0' J1' HstG0).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [exact Hag | exact (HK rhoE tp tr md HJ)].
  - eapply etriple_conseq; [intros w Hw; exact Hw | | apply (seg3_dir_ex J1' rhoE tp HstG1)].
    intros w Hw. exact (LQA_unG' J1 NF NF rho _ tp _ w Hw).
Qed.
End ReadDir.
End Icpt_read_proof.

(* [comment removed for export] *)
Module Icpt_memchr.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "rw"; "holds"; "agree_below"; "eval"; "SAlu"; "SLit"; "SVar"; "sprop_below"; "SPNot"; "sobj"; "sprop_eqb"; "ss_next"; "sv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Logic"; "eq"; "and"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "lt"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA"; "FirstNul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "ok_frameA"; "stableA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr.MCI"; "Jf"; "Jmc"; "Jz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "Posts_mci"; "GEU65"; "Pre_mci"; "ENDA"; "P_mci"; "big_facts"; "facts_mci"; "rip8_facts"; "sX"; "s_call"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr.ZF"; "mciZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S20S0S0SfS1A1S4R4R3R2A3S13S10S3eS1S9R5A1R2A3S11A3S1eS1S3R5A1M0R3A3S1eS1G0R4A3F_;F_;F_;FF;Fr2;Fr1;Fn;").
Proof.
  intros n r1 r2 F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n r1 r2 p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.
Lemma agree_below_le' : ltac2:(tb__ "0|0|
S20S20S0S0S40R4R3A2S4R4R3R2A3S4R6R4R3A3F_;F_;Fr2;Fr1;Fm;Fn;").
Proof. intros n m r1 r2 Hle (A & B & C). split; [intros i Hi; apply A; lia|]. split; assumption. Qed.
Lemma SPA_add_facts : ltac2:(tb__ "0|0|
S2aS0SfS15Q40A1A1SfS1A1S3bS21S1eS1S3R5A1R3A3S13S10S3eS1S9SdS3cR3A1A1A1R4A3S11A3S26S12R8R4R7R6R3A6S26S12R9S47R6R5A2R8R7R4A6F_;F_;F_;Fw;FA;FF;Ftp;Frho;FJ;").
Proof. intros J rho tp F A w HF Hb [Hsm HJ]. split; [apply smatchA_add_facts; assumption | exact HJ]. Qed.

Lemma triple_pre : ltac2:(tb__ "0|1|
S21OF_;S22OS22S21R4R1A1R4F_;Fw;R3S24S12R6R5R3A4M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.
Lemma etriple_pre : ltac2:(tb__ "0|2|
S21OF_;M0OG0S21R4R1A1R4F_;Fw;R3S23S12R5R3A3M1F_;G1F_;F_;FQ;FX;FP;").
Proof. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.

Lemma holds_fact : ltac2:(tb__ "0|0|
S0SfS1A1S1S1eS1S3R3A1R2A3S13S10S3fS1ScR2A1R3A3S11A3S3R5R3A2F_;F_;Fq;Ffacts;Frho;").
Proof.
  intros rho facts q HF H. apply existsb_exists in H as (p & Hp & E). apply sprop_eqb_sound in E. subst p.
  exact (proj1 (Forall_forall _ _) HF _ Hp).
Qed.

Section ZF.
Variable r : valuation.
Let XB := bv_unsigned (rw r 18). Let XL := bv_unsigned (rw r 19). Let XO := bv_unsigned (rw r 20).
Let z := bv_unsigned (rw r 16). Let A := bv_unsigned (rw r 17). Let n := bv_unsigned (rw r 14).
Definition mciZ : Prop := ltac2:(tb__ "0|2|
S14S18S17Vz;Z10A2VA;A2S14S18VA;S19Z2M0Z3eA2M1A2S14S18S17VXO;VA;A2VXL;A2S14S18VXL;S19G0Z28A2A2S14S18S17VXB;VXL;A2S19G0Z2fA2A2S14S1aVz;Vn;A2S18Vn;G1A2A2A2A2A2A2A2").
Lemma two62_eq : two62 = 2 ^ 62. Proof. reflexivity. Qed.
Lemma facts_mciZ : ltac2:(tb__ "0|0|
S1eS1S3Vr;A1S36A3S42F_;").
Proof.
  intros HF. unfold facts_mci in HF.
  apply Forall_cons_iff in HF as [F1 HF]. apply Forall_cons_iff in HF as [F2 HF]. apply Forall_cons_iff in HF as [F3 HF].
  apply Forall_cons_iff in HF as [F4 HF]. apply Forall_cons_iff in HF as [F5 HF]. apply Forall_cons_iff in HF as [F6 HF].
  apply Forall_cons_iff in HF as [F7 HF]. apply Forall_cons_iff in HF as [F8 HF]. apply Forall_cons_iff in HF as [F9 HF].
  apply Forall_cons_iff in HF as [F10 HF]. apply Forall_cons_iff in HF as [F11 HF]. apply Forall_cons_iff in HF as [F12 HF].
  apply Forall_cons_iff in HF as [F13 HF]. apply Forall_cons_iff in HF as [F14 HF]. apply Forall_cons_iff in HF as [F15 HF].
  apply Forall_cons_iff in HF as [F16 HF]. apply Forall_cons_iff in HF as [F17 HF]. apply Forall_cons_iff in HF as [F18 HF]. apply Forall_cons_iff in HF as [F19 HF].
  apply Forall_cons_iff in HF as [F20 HF]. apply Forall_cons_iff in HF as [F21 HF].
  pose proof (urange (rw r 14)). pose proof (urange (rw r 16)). pose proof (urange (rw r 17)). pose proof (urange (rw r 18)).
  pose proof (urange (rw r 19)). pose proof (urange (rw r 20)).
  unfold vXB, vXL, vXO in *.
  cbn [holds branch_taken eval] in F1, F2, F3, F4, F5, F11, F12, F13, F14, F15, F16, F17, F21. unfold bv_ltu in F1. apply Z.ltb_lt in F1.
  rewrite add_lit_val in F21. change (snorm 16) with 16 in F21.
  rewrite lit_unsigned in F15. rewrite lit_unsigned in F17. change ((2 ^ 47 - 64) mod 2 ^ 64) with (2 ^ 47 - 64) in F17.
  rewrite add_lit_val in F2. change (snorm 8) with 8 in F2.
  rewrite lit_unsigned in F3. change (8 mod 2 ^ 64) with 8 in F3.
  rewrite two62_eq, lit_unsigned in F4. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F4.
  rewrite two62_eq, lit_unsigned in F5. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F5.
  rewrite add_val in F11. rewrite lit_unsigned in F14. change ((2 ^ 40) mod 2 ^ 64) with (2 ^ 40) in F14.
  rewrite add_val, lit_unsigned in F16. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47) in F16.
  unfold mciZ. subst XB XL XO z A n.
  assert (E2 : (bv_unsigned (rw r 16) + 8) mod 2 ^ 64 = bv_unsigned (rw r 16) + 8).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 8) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 8) with ((bv_unsigned (rw r 16) + 8 - 2 ^ 64) + 1 * 2 ^ 64) in F2 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F2 by lia. lia. }
  rewrite E2 in F2.
  assert (E21 : (bv_unsigned (rw r 16) + 16) mod 2 ^ 64 = bv_unsigned (rw r 16) + 16).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 16) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 16) with ((bv_unsigned (rw r 16) + 16 - 2 ^ 64) + 1 * 2 ^ 64) in F21 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F21 by lia. lia. }
  rewrite E21 in F21.
  assert (E11 : (bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) mod 2 ^ 64 = bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) by (apply Z.mod_small; lia).
  rewrite E11 in F11.
  assert (E16 : (bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) mod 2 ^ 64 = bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) by (apply Z.mod_small; lia).
  rewrite E16 in F16.
  repeat split; lia.
Qed.
End ZF.

Lemma rip8_facts_hold : ltac2:(tb__ "0|3|
S0SeS1fS13S1fS16Q40M0S5R3R2A2A2R1A3S18Z0R2A2S18S17S17S16G0S2R5P14A2A2R3A2Z8A2S16G0S2R5P13M1A2A2A2S18S16G0S2R6G1A2A2S19Z2M2Z28A2A2S18S17S16G0S2R7P12A2A2S16G0S2R7G1A2A2A2S19G2Z2fA2A2S1eS1S3R8A1S37R7A1A3F_;F_;F_;F_;F_;Fk;Fn;Fr;").
Proof.
  intros r n k Hn Hk H1 H2 H3.
  pose proof (urange (rw r 18)) as R18. pose proof (urange (rw r 19)) as R19. pose proof (urange (rw r 20)) as R20.
  assert (U8 : bv_unsigned (eval r vXL8) = bv_unsigned (rw r 19) - 8).
  { unfold vXL8, vXL. apply (U_addc r (SVar 19) (-8)); [reflexivity | lia | lia]. }
  assert (UOn : bv_unsigned (eval r (SAlu ALU_ADD vXO n)) = bv_unsigned (rw r 20) + k).
  { unfold vXO. apply (U_add2 r (SVar 20) n); [reflexivity | exact Hn | lia]. }
  assert (UB8 : bv_unsigned (eval r (SAlu ALU_ADD vXB vXL8)) = bv_unsigned (rw r 18) + (bv_unsigned (rw r 19) - 8)).
  { unfold vXB. apply (U_add2 r (SVar 18) vXL8); [reflexivity | exact U8 | lia]. }
  assert (UBL : bv_unsigned (eval r (SAlu ALU_ADD vXB vXL)) = bv_unsigned (rw r 18) + bv_unsigned (rw r 19)).
  { unfold vXB, vXL. apply (U_add2 r (SVar 18) (SVar 19)); [reflexivity | reflexivity | lia]. }
  unfold rip8_facts.
  repeat (apply Forall_cons; [cbn [holds]; rewrite ?UOn, ?U8, ?UB8, ?UBL, ?Hn; try rewrite (U_lit64 r (2 ^ 40)) by lia;
                              try rewrite (U_lit64 r (2 ^ 47 - 8)) by lia; change (eval r vXB) with (rw r 18); change (eval r vXO) with (rw r 20); lia |]).
  apply Forall_nil.
Qed.

Section MCI.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hok : ok_frameA segs ok J0.
Hypothesis Hst0 : stableA segs NF J0.

Definition Jf (rho1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|1|
S0SfS15Q40A1A1M0SfS2cA1S2bS14S4S1dVrho1;R4A3S14S13G0R3Vtp;A3VJ0;Vrho1;Vtp;R2R1A4A2A2Lmd;Ltr;Lt;Lr;").
Definition Jz (rho1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|1|
S0SfS15Q40A1A1M0SfS2cA1S2bS14S13G0R3Vtp;A3VJ0;Vrho1;Vtp;R2R1A4A2Lmd;Ltr;Lt;L_;").
Definition Jmc (rho1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|1|
S0SfS15Q40A1A1M0SfS2cA1S2bS14S13G0R3Vtp;A3S14VJ0;Vrho1;Vtp;R2R1A4S25R4A1A2A2Lmd;Ltr;Lt;Lr;").

Lemma Jf_stable : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S20S40S1dR1A2S29S12R2S2dR4R3A2A3F_;Fn;Ftp;Frho1;").
Proof.
  intros rho1 tp n Hn r r' t tr md md' Hag Hme (H1 & H2 & H3). split; [|split; [exact H2|]].
  - eapply agree_below_trans; [exact H1 | eapply agree_below_le'; [exact Hn | exact Hag]].
  - subst t. eapply Hst0; [apply agree_below_refl | exact Hme | exact H3].
Qed.
Lemma Jz_stable : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S20S29S12R1S2fR3R2A2A3Fn;Ftp;Frho1;").
Proof. intros rho1 tp n r r' t tr md md' Hag Hme [-> H3]. split; [reflexivity|]. eapply Hst0; [apply agree_below_refl | exact Hme | exact H3]. Qed.
Lemma Jmc_stable : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S29S12S1dS2eR2R1A2A3Ftp;Frho1;").
Proof.
  intros rho1 tp r r' t tr md md' Hag Hme (-> & H3 & H4). split; [reflexivity|]. split.
  - eapply Hst0; [apply agree_below_refl | exact Hme | exact H3].
  - eapply FirstNul_agree; [| exact Hag | exact H4]. reflexivity.
Qed.
Lemma Jf_okf : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S28S12Vok;S2dR2R1A2A3Ftp;Frho1;").
Proof. intros rho1 tp r t tr ms md msv' (_ & -> & HJ). eapply Hok; eauto. Qed.
Lemma Jz_okf : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S28S12Vok;S2fR2R1A2A3Ftp;Frho1;").
Proof. intros rho1 tp r t tr ms md msv' [-> HJ]. eapply Hok; eauto. Qed.
Lemma Jmc_okf : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S28S12Vok;S2eR2R1A2A3Ftp;Frho1;").
Proof. intros rho1 tp r t tr ms md msv' (-> & HJ & _). eapply Hok; eauto. Qed.

Lemma FirstNul_call : ltac2:(tb__ "0|0|
S0SfSbA1S41S25R3A1S25S44S43R4R3R2A3S39A2A1F_;Fms;FR;Frho;").
Proof.
  intros rho R ms [H0 H1]. destruct shape_call as (_ & _ & _ & S16). unfold FirstNul.
  change (rw (rho_sub (rho_absorb rho R ms) s_call) 16) with (eval (rho_absorb rho R ms) (wsub_get s_call 16)). rewrite S16.
  cbn [eval rw rl rho_sub rho_absorb]. split; assumption.
Qed.

Section ClassFacts.
Variable r : valuation.
Hypothesis HFm : Forall (holds r) facts_mci.
Hypothesis H140 : ltac2:(tb__ "0|0|
S13S15Q40A1S2Vr;P8cA2S2Vr;P10A2A3").
Let z := bv_unsigned (rw r 16).

Lemma U_sX : ltac2:(tb__ "0|1|
S13S1fS16Q40M0S5Vr;S38A2A2S17S16G0S2Vr;P12A2A2S16G0S2Vr;P14A2A2A2A3").
Proof.
  destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)).
  unfold sX, vXB, vXO. apply (U_add2 r (SVar 18) (SVar 20)); [reflexivity | reflexivity | lia].
Qed.
Lemma U_z1 : ltac2:(tb__ "0|1|
S13S1fS16Q40S5Vr;S6S3aS8P8cA1S7Z1M0A1A3A2A2S17Vz;G0A2A3").
Proof. pose proof (urange (rw r 16)). destruct (facts_mciZ r HFm) as (Z1 & Z2 & _). apply (U_addc r (SVar 140) 1 z); [cbn [eval]; rewrite H140; reflexivity | lia | lia]. Qed.
Lemma U_ENDA : ltac2:(tb__ "0|1|
S13S1fS16Q40M0S5Vr;S33A2A2S17S17S16G0S2Vr;P12A2A2S16G0S2Vr;P14A2A2A2Vz;A2A3").
Proof.
  destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)).
  assert (A2 : bv_unsigned (eval r (SAlu ALU_ADD sX (SAlu ALU_ADD (SVar 140) (SLit 1)))) = bv_unsigned (rw r 18) + bv_unsigned (rw r 20) + (z + 1)).
  { apply (U_add2 r _ _ _ _ U_sX U_z1). lia. }
  unfold ENDA. rewrite (U_addc r _ (-1) _ A2); lia.
Qed.
Lemma post_facts_hold : Forall (holds r) post_facts.
Proof.
  destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 16)).
  unfold post_facts. constructor; [|constructor; [|constructor]]; cbn [holds].
  - change (eval r vXB) with (rw r 18). rewrite U_ENDA. lia.
  - rewrite (U_addc r ENDA 1 _ U_ENDA) by lia. unfold vXB, vXL. pose proof (urange (rw r 19)).
    rewrite (U_add2 r (SVar 18) (SVar 19) (bv_unsigned (rw r 18)) (bv_unsigned (rw r 19)) eq_refl eq_refl) by lia. lia.
Qed.
Lemma U_m64 : ltac2:(tb__ "0|1|
S13S1fS16Q40S5Vr;S6S3aS8P8cA1S7N40A1A3A2A2S1bS1cVz;Z40M0A2S19Z2G0A2A2A3").
Proof. cbn [eval]. rewrite add_lit_val, H140. change (snorm (-64)) with (-64). reflexivity. Qed.
Lemma GEU65_S : ltac2:(tb__ "0|0|
S18S17Vz;Z1A2Z40A2S3Vr;SaS31A1A2F_;").
Proof.
  intros Hz. pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64, (U_lit64 r 18446744073709551551) by lia.
  replace ((z - 64) mod 2 ^ 64) with (z - 64 + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia).
  destruct (Z.ltb_spec 18446744073709551551 (z - 64 + 2 ^ 64)); [cbn; congruence | lia].
Qed.
Lemma GEU65_B : ltac2:(tb__ "0|0|
S18Z41S17Vz;Z1A2A2S3Vr;S31A2F_;").
Proof.
  intros Hz. destruct (facts_mciZ r HFm) as (Z1 & Z2 & _). pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64, (U_lit64 r 18446744073709551551) by lia.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec 18446744073709551551 (z - 64)); [lia | reflexivity].
Qed.
Lemma big_facts_hold : ltac2:(tb__ "0|0|
S18Z41S17Vz;Z1A2A2S1eS1S3Vr;A1S35A3F_;").
Proof.
  intros Hz. destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 16)). pose proof (urange (rw r 20)).
  pose proof U_z1 as U141. change (SAlu ALU_ADD (SVar 140) (SLit 1)) with N1 in U141.
  unfold big_facts. apply Forall_app. split.
  2:{ apply (rip8_facts_hold r N1 (z + 1) U141); lia. }
  constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds]; unfold vXO, vXL.
  - pose proof (urange (rw r 19)). rewrite (U_add2 r (SVar 20) _ (bv_unsigned (rw r 20)) (z + 1) eq_refl U141) by lia. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141, (U_lit64 r 1) by lia. lia.
Qed.
End ClassFacts.

Lemma to_post : ltac2:(tb__ "0|0|
S3bS45S0S0SfS15Q40A1A1S0S21S13S10S3dR7S34R6A3S11A3S13S10S46R7S1dA2S11A3S4S1dR7R6A3S4S1dR7R5A3S26S12S2dR8R7A2RbR6R7R5A6S27S12VJ0;S1dRaR8S30R6A7F_;F_;F_;F_;F_;Fw;FrhoR;Ftp;Frho1;Frho;Fsp;FG;").
Proof.
  intros G sp rho rho1 tp rhoR w Hent Hid Hag1 HagR HS.
  pose proof (SPA_entails segs (Jf rho1 tp) NF G P_mci sp rhoR tp w Hent Hid (Jf_stable rho1 tp NF (Pos.le_refl _)) HS) as [Hsm (Hag & _ & HJ)].
  exists (mkLeafA P_mci RsSymJump), (rho_sub rhoR sp). split; [left; reflexivity|]. split.
  - eapply agree_below_trans; [exact Hag1 | exact Hag].
  - split; [exact Hsm|]. eapply Hst0; [exact Hag | apply mat_equiv_refl | exact HJ].
Qed.

Theorem mci_sum : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S25R2A1S24S12Vok;S26S12VJ0;S32R3R2A5S27S12VJ0;S1dR3R2S30A6A4F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct shape_call as (HnC & HlenP & HnP & _). destruct shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbF). destruct shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct ids_mci as [IdS IdB].
  apply (triple_pre ok _ (Forall (holds rho) facts_mci)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_mci w Hsm) | intros HF0].

  eapply (runA_tr segs ok FUEL_MCI CUTS_MCI Pre_mci _ J0 rho tp); [exact run_call | exact HlenP | exact Hok | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_mci Hag1 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF0) as HF1.
  eapply triple_conseq with (P := SPA segs (Jf rho1 tp) E_call rho1 tp);
    [intros w [Hsm HJ]; split; [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_soundA segs ok (Jf rho1 tp) (Jmc rho1 tp) (Jmc rho1 tp) (Jf rho1 tp) E_call Pre_memchr0 s_call R_call Posts_memchr0 _ rho1 tp efr_call chk_call).
  - intros rho2 tp2. apply (triple_pre ok _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (memchr0_sum ok (Jmc rho1 tp) rho2 tp2 (Jmc_okf rho1 tp) (Jmc_stable rho1 tp) HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [exact (proj1 HLK)|]. split; [reflexivity | exact HJ'].
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite imp_call. rewrite HnC in Hag'.
    apply (triple_pre ok _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_mci Hag' ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF1) as HF'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }

    eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_mci T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    +
      assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HF' H140)]. }
      eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_MCI CUTS_MCI T_S _ (Jf rho1 tp) rho' tp);
        [exact run_S | exact HlS | apply Jf_okf | rewrite HnS; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XS rhoR R_S G_S tp w xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post G_S sp_S rho rho1 tp rhoR w ent_S IdS Hag1 Hag3 HS).
    +
      assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HF' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HF' H140) | apply (big_facts_hold rho' HF' H140); rewrite Hz'; lia]. }
      eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_MCI CUTS_MCI T_B _ (Jf rho1 tp) rho' tp);
        [exact run_B | exact HlB | apply Jf_okf | rewrite HnB; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply triple_conseq with (P := SPA segs (Jf rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 1 (SLit (-2128)) _ tp w split_rip HS) | intros w Hw; exact Hw |].
      apply (call_soundA segs ok (Jf rho1 tp) (Jz rho1 tp) (Jz rho1 tp) (Jf rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp efr_rip chk_rip).
      * intros rho2 tp2. exact (region_sum ok (Jz rho1 tp) rho2 tp2 (Jz_okf rho1 tp) (Jz_stable rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (triple_pre ok _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_mci)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (runA_tr segs ok FUEL_MCI CUTS_MCI T_ripF _ (Jf rho1 tp) rho'' tp);
          [exact run_B2 | exact HlTF | apply Jf_okf | rewrite HnTF; apply Jf_stable; unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XB rhoR R_B G_B tp w xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post G_B sp_B rho rho1 tp rhoR w ent_B IdB Hag1 Hag3 HS).
Qed.

Theorem mci_sum_ex : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S25R2A1S23S12S26S12VJ0;S32R3R2A5S27S12VJ0;S1dR3R2S30A6A3F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct shape_call as (HnC & HlenP & HnP & _). destruct shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbF). destruct shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct ids_mci as [IdS IdB].
  apply (etriple_pre _ (Forall (holds rho) facts_mci)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_mci w Hsm) | intros HF0].

  eapply (erunA_tr segs FUEL_MCI CUTS_MCI Pre_mci _ J0 rho tp); [exact run_call | exact HlenP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_mci Hag1 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF0) as HF1.
  eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) E_call rho1 tp);
    [intros w [Hsm HJ]; split; [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_completeA segs (Jf rho1 tp) (Jmc rho1 tp) (Jmc rho1 tp) (Jf rho1 tp) E_call Pre_memchr0 s_call R_call Posts_memchr0 _ rho1 tp efr_call chk_call).
  - intros rho2 tp2. apply (etriple_pre _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (memchr0_sum_ex (Jmc rho1 tp) rho2 tp2 (Jmc_stable rho1 tp) HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [exact (proj1 HLK)|]. split; [reflexivity | exact HJ'].
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite imp_call. rewrite HnC in Hag'.
    apply (etriple_pre _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_mci Hag' ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF1) as HF'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }
    eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_mci T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    +
      assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HF' H140)]. }
      eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_MCI CUTS_MCI T_S _ (Jf rho1 tp) rho' tp);
        [exact run_S | exact HlS | rewrite HnS; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XS rhoR R_S G_S tp w xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post G_S sp_S rho rho1 tp rhoR w ent_S IdS Hag1 Hag3 HS).
    +
      assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HF' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HF' H140) | apply (big_facts_hold rho' HF' H140); rewrite Hz'; lia]. }
      eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_MCI CUTS_MCI T_B _ (Jf rho1 tp) rho' tp);
        [exact run_B | exact HlB | rewrite HnB; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 1 (SLit (-2128)) _ tp w split_rip HS) | intros w Hw; exact Hw |].
      apply (call_completeA segs (Jf rho1 tp) (Jz rho1 tp) (Jz rho1 tp) (Jf rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp efr_rip chk_rip).
      * intros rho2 tp2. exact (region_sum_ex (Jz rho1 tp) rho2 tp2 (Jz_stable rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (etriple_pre _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_mci)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (erunA_tr segs FUEL_MCI CUTS_MCI T_ripF _ (Jf rho1 tp) rho'' tp);
          [exact run_B2 | exact HlTF | rewrite HnTF; apply Jf_stable; unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XB rhoR R_B G_B tp w xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post G_B sp_B rho rho1 tp rhoR w ent_B IdB Hag1 Hag3 HS).
Qed.
End MCI.
End Icpt_memchr.

(* [comment removed for export] *)
Module Asan_memsetZ_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "holds"; "ss_facts"; "eval"; "ss_next"; "agree_below"; "rw"; "sprop_below"; "SLit"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "Forall"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "ok_frameA"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.Asan_memsetZ"; "FT"; "Posts_ms"; "E_reg"; "E_real"; "Pre_ms0"; "Pre_ms1"; "s_L_bk"; "s_L_in"; "F_L"; "E_L_bk"; "E_L_in"; "R_real"; "R_reg"; "base_ms"; "cuts_ms"; "s_real"; "s_reg"; "vcuts_ms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof"; "clsZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "cur"; "gs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "withGA"; "ax_add_facts"; "vna_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "P_ret"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "P_msz"; "Pre_mszA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.Asan_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr AMSZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Lemma base_ms_Z : ltac2:(tb__ "0|1|
S1SfS2S3R1A1S28A3S19S30R2PfP10P11A4S19S33Z1S11Q40S8R2P12A2A2M0A2S33G0S34Z2Z28A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. pose proof (urange (rw rho 18)) as RN.
  have_fact N1 HF (SPUle (SLit 1) vN). have_fact N2 HF (SPUle vN (SLit (2 ^ 40))).
  unfold vN in N1, N2. rewrite (U_lit64 rho 1) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia. cbn [eval] in N1, N2.
  split; [|lia].
  apply (opnd_Z rho 15 16 17). unfold opnd_facts.
  have_fact A1 HF (SPUle (add vOd vN) vLd). have_fact A2 HF (SPUle vOd vLd). have_fact A3 HF (SPUle vN vLd).
  have_fact A4 HF (SPUle vLd (SLit (2 ^ 40))). have_fact A5 HF (SPUle (SLit 4096) vBd).
  have_fact A6 HF (SPUle (add vBd vLd) (SLit (2 ^ 47 - 8))). have_fact A7 HF (SPUle vBd (SLit (2 ^ 47 - 8))). have_fact A8 HF (SPAlign 15 3).
  unfold vBd, vLd, vOd in *. repeat (constructor; [assumption|]). constructor.
Qed.

Lemma FT_Z_ms : ltac2:(tb__ "0|1|
S1SfS2S3R1A1S1bA3S19S30R2PfP10P11A4S19S33Z1S11Q40S8R2P12A2A2M0A2S33G0S34Z2Z28A2A2A2A2F_;Frho;").
Proof. intros rho HF. unfold FT in HF. apply Forall_cons_iff in HF as [_ HB]. exact (base_ms_Z rho HB). Qed.

Ltac split_mid HF HX HT := cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Section Glue.
Variable rho : valuation.

Lemma glue_L_in : ltac2:(tb__ "0|0|
SfS2S3Vrho;A1S4S12S25A1A1A3SfS2S3S31Vrho;S22A2A1S23A3F_;").
Proof.
  intros HF. unfold E_L_in in HF. split_mid HF HX HT.
  destruct (FT_Z_ms rho HT) as (ZD & ZN).
  destruct (in_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_L_in).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 17)) as R17.
  change F_L with (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.F_L vBd vLd lastd).
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E15, ?E16, ?E17; unfold HSE in *; lia.
Qed.

Lemma glue_L_bk : ltac2:(tb__ "0|0|
SfS2S3Vrho;A1S4S12S24A1A1A3SfS2S3S31Vrho;S21A2A1S23A3F_;").
Proof.
  intros HF. unfold E_L_bk in HF. split_mid HF HX HT.
  destruct (FT_Z_ms rho HT) as (ZD & ZN).
  change F_L with (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.F_L vBd vLd lastd) in HX |- *.
  destruct (bk_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_L_bk).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E15, ?E16, ?E17, ?E141; unfold HSE in *; try lia.
Qed.

Lemma meas_L_in : ltac2:(tb__ "0|0|
S1aS10Q40A1S5S31Vrho;S22A2S35A2S5Vrho;S36A2A3").
Proof. reflexivity. Qed.
Lemma meas_L_bk : ltac2:(tb__ "0|0|
S1aS10Q40A1S5S31Vrho;S21A2S35A2S5Vrho;S43S35SaZ1A1A2A2A3").
Proof. reflexivity. Qed.
End Glue.

Lemma FT_of_Ereg : ltac2:(tb__ "0|0|
S1SfS2S3R1A1S4S12S1dA1A1A3SfS2S3R2A1S1bA3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_reg mid_state mkA] in HF. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S1SfS2S3R1A1S4S12S1eA1A1A3SfS2S3R2A1S1bA3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. exact HF. Qed.
Lemma next_E_ms : ltac2:(tb__ "0|0|
S19S41SeS6S12S1dA1A1A2S41SeS6S12S1eA1A1A2A2").
Proof. split; cbv; congruence. Qed.
Lemma FT_below190 : forallb (sprop_below 190) FT = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FL_below190 : forallb (sprop_below 190) F_L = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FT_below_T : ltac2:(tb__ "0|0|
S19S1aScS40S2S9S6S12S3eS2bS44S42S1dS27A5A1A1A1S1bA3SdA3S1aScS40S2S9S6S12S3eS2aS47S45S46A1S1eS26A5A1A1A1S1bA3SdA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ids_ms : ltac2:(tb__ "0|0|
S19S1aScS32S22SeA2SdA3S1aScS32S21SeA2SdA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma FT_of_Ereg_cls : ltac2:(tb__ "0|0|
SbS2A1S1SfS2S3R1A1S4S12S3cR2S1dA2A1A1A3SfS2S3R2A1S1bA3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_reg mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1SbS2eA1S2dVJ;R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_ms_sound : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S13S3fS13R1S29A3S1S38S0Vok;S14S0S3bS1S7SeR6R1A3Lr;VJ;A2R3R1R4A5S15S0VJ;SeR5R4S1cA6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT. destruct ids_ms as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELS cutpcs_ms NF cuts_ms exits_ms (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_ms) tp HokG HstG check_ms); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply exit_postA. in_nth 0.
  - apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_reg rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_reg_hi Pre_rip s_reg R_reg Posts_rip FT Hst fr_reg_hi cc_reg_hi (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   cuts_ms _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 1]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_reg_lo Pre_rip_lo s_reg R_reg Posts_rip FT Hst fr_reg_lo cc_reg_lo (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   cuts_ms _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 1]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_mszA s_real R_real Posts_mszA FT Hst fr_real cc_real (proj2 next_E_ms) FT_of_Ereal FT_below190
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_T)) | or_intror F => match F with end end)
             cuts_ms _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memsetZ_sumA ok' Jq Ho Hs rho1 tp1).
    + intros L [<-|[]]. in_nth 2.
  - apply (exit_reenterA segs ok _ NF cuts_ms _ E_L_in CL_0 F_L s_L_in tp);
      [in_nth 3 | exact ent_L_in | exact I1 | exact HstG | exact FL_below190 | intros r tp' tr md _ HF; exact (glue_L_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_ms _ E_L_bk CL_0 F_L s_L_bk tp);
      [in_nth 3 | exact ent_L_bk | exact I2 | exact HstG | exact FL_below190 | intros r tp' tr md _ HF; exact (glue_L_bk r HF)].
Qed.

Theorem asan_memset_core_sum1 : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S38S0Vok;S14S0VJ;S20R2R1A5S15S0VJ;SeR2R1S1cA6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ms1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_ms_sound rho tp Pre_ms1). left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1SbS2eA1S2dVJ;R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_ms_complete : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S3aS3fS3aR1S2cA3S1S37S0S14S0S3bS1S7SeR6R1A3Lr;VJ;A2S3dR3A1R1R4A5S15S0VJ;SeR5R4S1cA6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT. destruct ids_ms as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELS cutpcs_ms NF vcuts_ms vexits_ms (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_ms) tp HstG); [ | exact echeck_ms | | exact HinT].
  { intros m Hm. unfold vcuts_ms in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_ms Posts_ms (mkVNA P_ms 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_reg rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_reg_hi Pre_rip s_reg R_reg Posts_rip FT Hst fr_reg_hi cc_reg_hi (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   vcuts_ms _ (mkVNA E_reg_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 79 (SLit (2 ^ 63))); split; [in_nth 1|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_reg_lo Pre_rip_lo s_reg R_reg Posts_rip FT Hst fr_reg_lo cc_reg_lo (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   vcuts_ms _ (mkVNA E_reg_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 79 (SLit (2 ^ 63))); split; [in_nth 1|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_mszA s_real R_real Posts_mszA FT Hst fr_real cc_real (proj2 next_E_ms) FT_of_Ereal FT_below190
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_T)) | or_intror F => match F with end end)
             vcuts_ms _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memsetZ_sumA_ex Jq Hs rho1 tp1).
    + intros L [<-|[]]. exists (mkVNA T3 39 (SLit (2 ^ 63 + 8))). split; [in_nth 2|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ NF vcuts_ms _ (mkVNA E_L_in 101 gs) (mkVNA CL 100 cur) F_L CL_0 s_L_in tp);
      [in_nth 3 | reflexivity | exact ent_L_in | exact I1 | exact HstG | exact FL_below190
      | intros r tp' tr md _ HF; split; [exact (glue_L_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_ms _ (mkVNA E_L_bk 101 (add cur (SLit 1))) (mkVNA CL 100 cur) F_L CL_0 s_L_bk tp);
      [in_nth 3 | reflexivity | exact ent_L_bk | exact I2 | exact HstG | exact FL_below190
      | intros r tp' tr md _ HF; split; [exact (glue_L_bk r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.

Theorem asan_memset_core_sum1_ex : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S37S0S14S0VJ;S20R2R1A5S15S0VJ;SeR2R1S1cA6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ms1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_ms1 with (vna_state (mkVNA Pre_ms1 200 (SLit 0))).
  apply (cfg_ms_complete rho tp). left; reflexivity.
Qed.
End SumEx.

Lemma SPA_ms01 : ltac2:(tb__ "0|0|
S16S1SbS10Q40A1A1S39S14S0R4S1fR3R2R1A6S14S0R5S20R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_ms0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_ms0 mkA] in HF.
  destruct (base_ms_Z rho HF) as (ZD & ZN). pose proof ZD as ZD'. unfold opZ in ZD'. cbv zeta in ZD'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 18)).
  destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  constructor; [|constructor]. unfold xor_fact.
  apply (xor_fact_Z rho dst (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))).
  - exact (V_opd 15 16 17 rho ZD ZN).
  - lia.
Qed.

Theorem asan_memset_core_sum : ltac2:(tb__ "0|1|
S39OF_;S16S1SbS10Q40A1A1M0S18S0R4R3A3S17S0SeR4A3S1G0SbS2eA1S2dR9R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S38S0R7S14S0R6S1fR5R4A5S15S0R6SeR5R4S1cA6A4F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD.
  eapply triple_conseq; [intros w Hw; exact (SPA_ms01 J rho tp w Hw) | intros w Hw; exact Hw | apply asan_memset_core_sum1; assumption].
Qed.

Theorem asan_memset_core_sum_ex : ltac2:(tb__ "0|1|
S16S1SbS10Q40A1A1M0S17S0SeR3A3S1G0SbS2eA1S2dR8R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S37S0S14S0R5S1fR4R3A5S15S0R5SeR4R3S1cA6A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD.
  eapply etriple_conseq; [intros w Hw; exact (SPA_ms01 J rho tp w Hw) | intros w Hw; exact Hw | apply asan_memset_core_sum1_ex; assumption].
Qed.
End Asan_memsetZ_proof.

