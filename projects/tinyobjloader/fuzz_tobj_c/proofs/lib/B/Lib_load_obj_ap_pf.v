(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "cons"; "nil"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "holds"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf"; "P0_hp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hp"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ap"; "kept_p"; "PDk_p"; "R_p"; "T_p_ok"; "E_p"; "Xk_p"; "passed_p"; "rate_gp"; "s_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ap.HP"; "Pre_hp"; "nd0"; "Posts_hp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ap_eqs"; "Xs_p"; "Ys_p"; "cutsP"; "Lok_p"; "nd_p_okX"; "s_latch_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "bd_nn"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex";
"alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_ap Lib_load_obj_ap_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HPAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S37S1S3SfA1M0S13OF_;M1A2M2G2S3cS6G0G1R1A3S7G0G1R1A3A2Lp;S54A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_p : nd_am HP.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_p : ltac2:(tb__ "0|1|
S37S1S10S1aA2M0G0S2cS20S24S7S10S1aR1A3A1S1dA3Ld;S61A3"). Proof. repeat constructor. Qed.
Lemma P0_hp_mono : ltac2:(tb__ "0|2|
S3S1SeSeA2M0A1M1G1G1S3S1G0SeA2A1S13G0S34G0R1R5A3S34G0R2R5A3F_;Fbn;S31R6R5R3R2A4S31R7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & E). split; [|exact E]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma pay_p : ltac2:(tb__ "0|0|
S13S37S15S16R1A1S17S11S4eA1A1A3S6cS62R2A2S2bS35S6eS63R3A2S6eS62R3A2A2S2bS35S6dS63R3A2S6dS62R3A2A2S6cS63R3A2A2A2F_;F_;Fr;").
Proof.
  intros r HF _. pose proof ap_checks_pay as (_ & _ & _ & EX & EY & EQ & _). rewrite EX, EY. rewrite EQ.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 480) (SVar 481))) F6. fact HF (SPUle (SAlu ALU_ADD (SVar 762) (SVar 476)) (SAlu ALU_ADD (SVar 440) (SVar 760))) F7.
  fact HF (SPUle (SVar 440) (SLit 4294967295)) F8. fact HF (SPUle (SVar 762) (SVar 763)) F9. fact HF (SPUle (SVar 763) (SLit 4294967295)) F10.
  fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 480) (SVar 481))) F11.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11. rewrite uval_lit in F1, F3, F8, F10 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 762)) as R762. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 440)) as R440. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428.
  pose proof (uval_range r (SVar 431)) as R431. pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 437)) as R437.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F12. rewrite h_ule, uval_lit in F12 by lia.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  rewrite E2 in F6, F11.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 762) (SVar 476)) = uval r (SVar 762) + uval r (SVar 476)) by (apply uval_add_small; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 440) (SVar 760)) = uval r (SVar 440) + uval r (SVar 760)) by (apply uval_add_small; lia).
  rewrite E3, E4 in F7.
  unfold LAr, LAX, LAK, LAXK, A1, AK1, pLNL, pPOS, pNX, vLEN. cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite E2.
  split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?E2; lia.
Qed.

Lemma rate_gp_holds : ltac2:(tb__ "0|0|
S13S37S15S16R1A1S17S11S4eA1A1A3S37S15S16R2A1SbS15S52ScS15A1A3A3F_;Fr;").
Proof.
  intros r HF. pose proof ap_checks_pay as (_ & _ & _ & _ & _ & EQ & _).
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 480) (SVar 481))) F6. fact HF (SPUle (SVar 586) (SVar 490)) F7. fact HF (SPUle (SVar 476) (SVar 760)) F8.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9. rewrite uval_lit in F1, F3, F9 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 586)) as R586. pose proof (uval_range r (SVar 490)) as R490.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E2 in F6.
  assert (ES : uval r (SAlu ALU_SUB qCURp pCP) = uval r (SVar 760) - uval r (SVar 476)) by (rewrite EQ; unfold pCP; apply uval_sub_le; exact F8).
  constructor; [|constructor]. unfold rate_gp, gPI', pE0, gPI, pPOS, pLNL. apply (proj2 (h_ule _ _ _)).
  rewrite uval_add_small by (rewrite ES; lia). rewrite ES.
  rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S79S13S3S27Q40A1A1S41OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S78S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SeS71VCST;R1A2S2bS35Z0R2A2S36R2S74A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SeS71VXGL;R1A2S2bS35Z0R2A2S36R2S74A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SeS7cR1A1S71VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1SeSeA2SeA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF0 : ccount 0 (map fst FF) = 0%nat.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S13OFr;") := ltac2:(tb__ "0|0|
S7dVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1eVAInv;VCST;VXGL;S68VKc;Vrho0;VP0;VFB;VFF;VBX;S1bVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3bVAInv;VCST;VXGL;S68VKc;Vrho0;VP0;VFB;VFF;VBX;S1bVPhi;Vnd;Ad").

Lemma HIN_p : ltac2:(tb__ "0|1|
S13S4aS79S13S3S27Q40A1A1S41S37S15S16R6A1S17S11S4fA1A1A3VP0;Vrho0;A1S72S68Vrho0;R8A3VAInv;R7R6R5R4A4S1fVrho0;R8A2S7fRbS7bS7aR9A1A1A2S21VFB;RaA2S22VFF;RbA2S26VFB;RcReS9S1S14S14A2S4bS51A3M0A4S80RfG0A2S81R10G0A2S23VFF;RfR11S33A4S2bS85VCST;Vrho0;VFB;VFF;R12S4bS33S4dA8S2bS86VCST;VXGL;Vrho0;VFB;VFF;R12S4bS33S50A9S31VCST;S7eVFB;R12S4bA3S84VFF;R12S33A3S3dS3eR12S4dR11A3S53A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof ap_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_p) by (apply (tvinA_sublist FB Ai rho (kept_p ++ passed_p)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_p) by (exact (tvd_app_l rho kept_p passed_p HD)).
  assert (HZk : tvz rho kept_p) by (apply (tvz_sublist rho (kept_p ++ passed_p)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_p frL extra_p R_p rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_p in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_p frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_p frL o a HF CLN HT0 HZk lines_in_kept_p HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_p frL xextraLO Xk_p rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_p frL r a Hav HP0 HE Ha).
  - pose proof ap_checks as (_ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_hp, P0_builder. rewrite !rw_call'.
    change (wsub_get s_p 15) with vBUF. change (wsub_get s_p 18) with vLEN. change (wsub_get s_p 12) with bA. change (wsub_get s_p 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_p rho R_p ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho kept_p) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_p) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF0. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SeS3S27Q40A1A1S2dF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S29S10S13S3S27Q40A1A1S2dS37S15S16R3A1S17S11R4A1A1A3VTR;S28S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2dS2dS2dS30R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2dOS2dS30R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S29S29S10S10S3fS3S19A1M0S3S1S10S58A2M1A1S3S1S14S14A2M2A1S2dS13S3S27Q40A1A1M3G2S34G2R1R5A3S34G2R2S12RbA1A3F_;Fr;S2cSdG0A1S5bRaR9R8A3S8G0R7A2A3S2cSaS5aRbRaR9R8S38G1S10S6S10S58A2R7A4A5S5A3S13G3VTR;S28S0RfRdR2R1A5S57S0S18S11RdA1A1R2R1RaA5A2Ftp1;Frho1;S3S42A1M4S4aS41S2aS0R9R8R10S2G4S5cR3S5dR2R1A2A4A5R13RaR9R4R2A4R13S3dS3eRbRfS40R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S10S58G4S4aS41S13G3G4S4aS41S34G1S2S10S58RaR9A4R14A3S2aS0R12R11R19S2G4S5cR9S5dR8R7A2A4A5R1cR13R12RaR8A4S72S18S11R1aA1A1S3dS3eR14R18S40R9R13RaA3A3R19A2R8A3S2aS0R9R8ReS2G4S5cR7S5dR6R5A2A4A5ReS3dS3eR16R1aS40RbR15RcA3A3R1bA2R15RaR9R8R6A6S2bS82R17S40RcR16RdA3R1bR1cR1dR10R1eR19RbA9S13S73R18S40RdR17ReA3R1cR1dS11R1eA1S11R1fA1S11R11A1R1RcA9VTR;S28S0S59R11S3dS3eR19R1dS40ReR18RfA3A3R1eA2R18RdRcA5S83R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S28S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S13OF_;S1aS10S13S3S27Q40A1A1S2dR6R3A1VTR;S28S0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S28S0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHP : ltac2:(tb__ "0|1|
S3S1SeSeA2M0A1S3S1G0SeA2A1S6bS13S3S27Q40A1A1S6aZ5R3A2VTR;S28S0S1cVAInv;VCST;VXGL;VKc;S31VCST;R6R5A3R6R5R4S1bS6fS55S5S60A3AaS5fR3R2A5S57S0S5eR3R2S70VAInv;VCST;VXGL;VKc;S31VCST;A1S1bS4cR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
S10S1aS4S1SeS14A2M0S13S3S27Q40A1A1M1SeG1S34S1S1S1S10S1aA2M2S4A2M3G0A2S2G3G0S2G2S4S2S10S1aR8R7A4R6A4R5A4S64A3S3aS54R7R5A3S2bS35Z0S39S2G3G0S2G2S4S2S10S1aRaR9A4R8A4R7A4R6A2M4A2S36G4R4A2A2VTR;S28S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_p : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0VTR;S28S0VJAFv;S32S43A2S49R3R2A5VFAM;S39S2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS49S43A4U1A4S2SeS14S44S45Z11S47A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof ap_checks as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnx).
  pose proof ap_checks2 as (_ & _ & CLN & _).
  set (ndv := NDA tv_p frL bd_p (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_p rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) xf_p rho E_hp E_p tp w Cxf).
    unfold ndv, tv_p. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_p _ E_hp rho tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hp rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_p HF CLN HTK HZ). unfold tv_p. apply in_or_app. left. exact lines_in_kept_p. }
  intros Hdnz.

  unfold ndv, tv_p.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_hp CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HP.Pre_hp (ndh h0 true HP.nd0) PDk_p NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHP eq_refl
           E_p s_p R_p Xk_p rho tp kept_p passed_p frL bd_p brest_p (AHead pH true) (FAM (efmeasA (E_hp, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  -
    unfold payA. apply (pay_okF_split _ _ _ _ bd_p _ payC_p payX_p payY_p PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_p rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_p frL rho' HK lines_in_kept_p Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof ap_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & RT & Rfb).
    cbn [PDk_p liftPD PDh HP.Posts_hp map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_p_f) T_p_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p_f) (xfb_p T_p_f0) rho' T_p_f0 B_p_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof ap_checks_payf as (QP1 & QP2 & QPay & _ & _).
      apply (TR_pre (SPA segs (JAv nd_p_fX) T_p_f rho' tp')).
      { intros w Hw. unfold nd_p_fX, nd_p_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p_f frL (AHead pH true) bd_p_f commf_p Xf_p Yf_p bd_p_fX _ T_p_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_p_f nd_p_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hp T_p_f ndA1 nd_p_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_p_ok) T_p_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p_ok) (xfb_p T_p_ok0) rho' T_p_ok0 B_p_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof ap_checks_pay as (PQ1 & PQ2 & PWy & _).

      apply (TR_pre (SPA segs (JAv nd_p_okX) T_p_okR rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb | intros tr md _ _; apply Forall_app; split; [exact (rate_gp_holds rho' HFo) | exact HFo]].
        unfold nd_p_okX, nd_p_ok in *.
        exact (SPA_bd_repay_sem AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p_ok frL (AHead pH true) bd_p_ok comm_p Xs_p Ys_p bdX_p _ T_p_ok rho' tp' w PQ1 PQ2 PWy HFo (pay_p rho') Hw). }
      apply (CUTV T_p_okR nd_p_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hp T_p_okR ndA1 nd_p_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Lemma Lok_p_latch : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1S30S32R3A1S28S0VJAv;S66A1S65R4R3R2A6S2bS32S3dR5S67A2M0A1S28S0VJAv;S46A1S56G0R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof ap_checks_exit as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & _ & _ & Xperm).
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lok_p X_latch s_latch_p nd_p_okX tv_p (bdX 0) (AHead pH true) tblB V_B rho tp w
              tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HP HS) as [HP' HS'].
  split; [exact HP'|]. unfold ndX0, ndL. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p tvL frL (bdX 0) (AHead pH true) X_latch _ tp w Xperm HS').
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S25S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S76S0S75VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1M0G0S2fS0Vok;S28S0VJAFv;S32S46A2S56R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1M0G0S2fS0Vok;S28S0VJAFv;S32S48A2S69R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHP_T : ltac2:(tb__ "0|1|
S3S1SeSeA2M0A1S3S1G0SeA2A1S6bS13S3S27Q40A1A1S6aZ5R3A2S2fS0Vok;S28S0S1cVAInv;VCST;VXGL;VKc;S31VCST;R6R5A3R6R5R4S1bS6fS55S5S60A3AaS5fR3R2A5S57S0S5eR3R2S70VAInv;VCST;VXGL;VKc;S31VCST;A1S1bS4cR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_p.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_hp CST) PTrue HP.Pre_hp (ndh h0 true HP.nd0) (PDh HP.Posts_hp h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_hp CST) PTrue HP.Pre_hp HP.nd0 HP.Posts_hp NPH h0 true h0_ltH HamC_p HamPD_p (P0_hp_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_p_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S10S1aS4S1SeS14A2M0S13S3S27Q40A1A1M1SeG1S34S1S1S1S10S1aA2M2S4A2M3G0A2S2G3G0S2G2S4S2S10S1aR8R7A4R6A4R5A4S64A3S3aS54R7R5A3S2bS35Z0S39S2G3G0S2G2S4S2S10S1aRaR9A4R8A4R7A4R6A2M4A2S36G4R4A2A2S2fS0Vok;S28S0VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsP) (map efdrop exitsP) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertP_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsP In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1) ok). intros HP1.
    eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho1 s_latch_p) tp1 tp0')].
    intros w Hw. destruct (Lok_p_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_p tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ap_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_p_T : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1M0G0S2fS0Vok;S28S0VJAFv;S32S43A2S49R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_p (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHP_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S77S0S75VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
SeS3S27Q40A1A1S2dF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SeSeS3S27Q40A1A1S30S35R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0S2eS0S28S0VJAFv;S32S46A2S56R3R2A5VFAM;S39S2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS56S46A4U1A4S2SeS14S44S45Z1S47A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0S2eS0S28S0VJAFv;S32S48A2S69R3R2A5VFAM;S39S2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS69S48A4U1A4S2SeS14S44S45Z1S47A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHP_E : ltac2:(tb__ "0|1|
S3S1SeSeA2M0A1S3S1G0SeA2A1S6bS13S3S27Q40A1A1S6aZ5R3A2S2eS0S28S0S1cVAInv;VCST;VXGL;VKc;S31VCST;R6R5A3R6R5R4S1bS6fS55S5S60A3AaS5fR3R2A5S57S0S5eR3R2S70VAInv;VCST;VXGL;VKc;S31VCST;A1S1bS4cR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_p.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_hp CST) PTrue HP.Pre_hp (ndh h0 true HP.nd0) (PDh HP.Posts_hp h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_hp CST) PTrue HP.Pre_hp HP.nd0 HP.Posts_hp NPH h0 true h0_ltH HamC_p HamPD_p (P0_hp_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_p_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S10S1aS4S1SeS14A2M0S13S3S27Q40A1A1M1SeG1S34S1S1S1S10S1aA2M2S4A2M3G0A2S2G3G0S2G2S4S2S10S1aR8R7A4R6A4R5A4S64A3S3aS54R7R5A3S2bS35Z0S39S2G3G0S2G2S4S2S10S1aRaR9A4R8A4R7A4R6A2M4A2S36G4R4A2A2S2eS0S28S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsP exitsP (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertP_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsP In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    eapply etriple_conseq; [| intros w Hw; right; exact Hw |].
    2: { pose proof ap_checks_exit as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
         rewrite <- (efmeasA_VLA_sub X_latch Lok_p ndX0 nd_p_okX 1%nat 1%nat RL 1 s_latch_p rho1 W460 W467).
         exact (XLATCH (rho_sub rho1 s_latch_p) tp1 tp0'). }
    intros w Hw. destruct (Lok_p_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_p tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ap_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_p_E : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0S2eS0S28S0VJAFv;S32S43A2S49R3R2A5VFAM;S39S2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS49S43A4U1A4S2SeS14S44S45Z11S47A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_p (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHP_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
