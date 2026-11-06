(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "eval"; "ss_next"; "SAlu"; "SLit"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf"; "P0_vt"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "pow"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hvt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avt"; "kept_vt"; "PDk_vt"; "R_vt"; "E_vt"; "E_vt1"; "Xk_vt"; "avt_cell_new"; "avt_cell_old"; "passed_vt"; "room_vt"; "s_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avt.HVT"; "Pre_vt"; "nd0"; "Posts_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avt_eqs"; "cutsT2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1 Lib_handle_vt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_avt Lib_load_obj_avt_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HVTAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S3fS2S4S1A1M0S11OF_;M1A2M2G2S39S7G0G1R1A3S8G0G1R1A3A2Lp;S4fA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_vt : nd_am HVT.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vt : ltac2:(tb__ "0|1|
S3fS2SeS1bA2M0G0S31S21S25S8SeS1bR1A3A1S1eA3Ld;S67A3"). Proof. repeat constructor. Qed.
Lemma P0_vt_mono : ltac2:(tb__ "0|2|
S4S2S0S0A2M0A1M1G1G1S4S2G0S0A2A1S11G0S33G0R1R5A3S33G0R2R5A3F_;Fbn;S32R6R5R3R2A4S32R7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & E). split; [|exact E]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma uval_sll1 : ltac2:(tb__ "0|1|
S11S12S3bS6eR2R1A2S3eZ2M0Z3eA2A2S31S0S6eR3S18S7cR2S19Z1A1A3A2S3dG0S6eR3R2A2A2A3F_;Ft;Frho;").
Proof.
  intros rho t Ht. pose proof (uval_range rho t) as R. unfold uval in *. cbn [eval]. rewrite sll_val.
  change (1 mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sll1_add2_eq : ltac2:(tb__ "0|0|
S11S31S28Q40A1S16R1S58A2S16R1S57A2A3Frho;").
Proof.
  intros rho. unfold avt_cell_old, avt_cell_new, t1. apply bv_eq. cbn [eval].
  rewrite add_val, !sll_val, add_val, !lit_unsigned. change (1 mod 64) with 1. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  change (2 mod 2 ^ 64) with 2. change (1 mod 2 ^ 64) with 1.
  rewrite Zplus_mod_idemp_l. rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.

Lemma room_vt_holds : ltac2:(tb__ "0|0|
S11S3fS14S13R1A1S15SfS55A1A1A3S3fS14S13R2A1S5aA3F_;Frho;").
Proof.
  intros rho HF. pose proof avt_checks2 as (_ & _ & _ & CT & CN & CL & _).
  pose proof (holds_mem _ _ _ HF CT) as FT. pose proof (holds_mem _ _ _ HF CN) as FN. pose proof (holds_mem _ _ _ HF CL) as FL.
  rewrite h_ule in FT, FN, FL. rewrite uval_lit in FL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho c_avt) as RC.
  rewrite uval_add_small in FN by (rewrite uval_lit by lia; lia). rewrite uval_lit in FN by lia.
  assert (E1 : uval rho (SAlu ALU_SLL c_avt (SLit 1)) = 2 * uval rho c_avt) by (apply uval_sll1; lia).
  assert (E2 : uval rho (SAlu ALU_ADD (SAlu ALU_SLL c_avt (SLit 1)) (SLit 2)) = 2 * uval rho c_avt + 2) by (rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia); rewrite E1, uval_lit by lia; lia).
  assert (E3 : uval rho (kb 4 (SAlu ALU_ADD (SAlu ALU_SLL c_avt (SLit 1)) (SLit 2))) = 4 * (2 * uval rho c_avt + 2)) by (unfold kb; rewrite uval_mul_lit by (rewrite ?E2; lia); rewrite E2; reflexivity).
  unfold room_vt. constructor; [|constructor; [|constructor]]; apply (proj2 (h_ule _ _ _)).
  - rewrite uval_lit by lia. lia.
  - rewrite E3. rewrite uval_lit by (unfold B_EW, Lib_vec_reserve.B_EW; lia). unfold B_EW, Lib_vec_reserve.B_EW. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S79S11S4S28Q40A1A1S42OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S78SdVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S61VCST;R1A2S30S3aZ0R2A2S3bR2S74A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S61VXGL;R1A2S30S3aZ0R2A2S3bR2S74A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S0S7dR1A1S61VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S2S2S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF1 : ltac2:(tb__ "0|1|
S31S5S88Z1S40S2S2S0S0A2M0S0A2G0S7G0S0A2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S7eVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1fVAInv;VCST;VXGL;S69VKc;Vrho0;VP0;VFB;VFF;VBX;S1cVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S38VAInv;VCST;VXGL;S69VKc;Vrho0;VP0;VFB;VFF;VBX;S1cVPhi;Vnd;Ad").

Lemma HXpow : ltac2:(tb__ "0|0|
S0S30S3aS71R1A2S3bR1S3cS71Zb8A2A2A2S61VXGL;R2A2F_;Fa;").
Proof.
  intros a Ha. apply HXlits. apply (in_litsL_In _ 145856 184 a); [|unfold pow10_tab, ScanDoubleAddr.pow10_tab in Ha; cbn in Ha |- *; lia].
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.X_lits. cbn [In]. do 17 right. left. reflexivity.
Qed.

Lemma HIN_vt : ltac2:(tb__ "0|1|
S11S4eS79S11S4S28Q40A1A1S42S3fS14S13R6A1S15SfS54A1A1A3VP0;Vrho0;A1S72S69Vrho0;R8A3VAInv;R7R6R5R4A4S20Vrho0;R8A2S80RbS7bS7aR9A1A1A2S22VFB;RaA2S23VFF;RbA2S27VFB;RcReSaS2S12S12A2S51S59A3M0A4S81RfG0A2S82R10G0A2S24VFF;RfR11S35A4S30S86VCST;Vrho0;VFB;VFF;R12S51S35S53A8S30S87VCST;VXGL;Vrho0;VFB;VFF;R12S51S35S56A9S32VCST;S7fVFB;R12S51A3S85VFF;R12S35A3S4cS4bR12S53R11A3S5bA2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof avt_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_vt) by (apply (tvinA_sublist FB Ai rho (kept_vt ++ passed_vt)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vt) by (exact (tvd_app_l rho kept_vt passed_vt HD)).
  assert (HZk : tvz rho kept_vt) by (apply (tvz_sublist rho (kept_vt ++ passed_vt)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_vt frL extra_vt R_vt rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_vt in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_vt frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_vt frL o a HF CLN HT0 HZk lines_in_kept_vt HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_vt frL xextraLO Xk_vt rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_vt frL r a Hav HP0 HE Ha).
  - pose proof avt_checks as (_ & _ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_vt, P0_builder. rewrite !rw_call'.
    change (wsub_get s_vt 15) with vBUF. change (wsub_get s_vt 18) with vLEN. change (wsub_get s_vt 12) with bA. change (wsub_get s_vt 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_vt rho R_vt ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho kept_vt) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_vt) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF1. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S4S28Q40A1A1S2cF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2aSeS11S4S28Q40A1A1S2cS3fS14S13R3A1S15SfR4A1A1A3VTR;S29SdR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2cS2cS2cS2fR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2cOS2cS2fR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2aS2aSeSeS4dS4S1aA1M0S4S2SeS5dA2M1A1S4S2S12S12A2M2A1S2cS11S4S28Q40A1A1M3G2S33G2R1R5A3S33G2R2S10RbA1A3F_;Fr;S31ScG0A1S60RaR9R8A3S9G0R7A2A3S31SbS5fRbRaR9R8S40G1SeS7SeS5dA2R7A4A5S6A3S11G3VTR;S29SdRfRdR2R1A5S5cSdS17SfRdA1A1R2R1RaA5A2Ftp1;Frho1;S4S43A1M4S4eS42S2bSdR9R8R10S3G4S62R3S63R2R1A2A4A5R13RaR9R4R2A4R13S4cS4bRbRfS41R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SeS5dG4S4eS42S11G3G4S4eS42S33G1S3SeS5dRaR9A4R14A3S2bSdR12R11R19S3G4S62R9S63R8R7A2A4A5R1cR13R12RaR8A4S72S17SfR1aA1A1S4cS4bR14R18S41R9R13RaA3A3R19A2R8A3S2bSdR9R8ReS3G4S62R7S63R6R5A2A4A5ReS4cS4bR16R1aS41RbR15RcA3A3R1bA2R15RaR9R8R6A6S30S83R17S41RcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S73R18S41RdR17ReA3R1cR1dSfR1eA1SfR1fA1SfR11A1R1RcA9VTR;S29SdS5eR11S4cS4bR19R1dS41ReR18RfA3A3R1eA2R18RdRcA5S84R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S29SdR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S1bSeS11S4S28Q40A1A1S2cR6R3A1VTR;S29SdVJAv;R6A1R5R4R3A5R2A2F_;VTR;S29SdVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHVT : ltac2:(tb__ "0|1|
S4S2S0S0A2M0A1S4S2G0S0A2A1S6dS11S4S28Q40A1A1S6cZ5R3A2VTR;S29SdS1dVAInv;VCST;VXGL;VKc;S32VCST;R6R5A3R6R5R4S1cS6fS50S6S66A3AaS65R3R2A5S5cSdS64R3R2S70VAInv;VCST;VXGL;VKc;S32VCST;A1S1cS52R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
SeS1bS5S2S0S12A2M0S11S4S28Q40A1A1M1S0G1S33S2S2S2SeS1bA2M2S5A2M3G0A2S3G3G0S3G2S5S3SeS1bR8R7A4R6A4R5A4S68A3S37S4fR7R5A3S30S3aZ0S36S3G3G0S3G2S5S3SeS1bRaR9A4R8A4R7A4R6A2M4A2S3bG4R4A2A2VTR;S29SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_vt : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0VTR;S29SdVJAFv;S34S44A2S4aR3R2A5VFAM;S36S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS4aS44A4U1A4S3S0S12S45S46Z11S47A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof avt_checks as (Cxf & CE & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & Chand & Cpay & Cnb & Cbr & Cnp & Cnx & Cfb).
  pose proof avt_checks2 as (_ & _ & CLN & _).
  set (ndv := NDA tv_vt frL bd_vt (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_vt rho tp)).
  { intros w Hw. rewrite <- CE. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_vt rho E_hvt E_vt1 tp w Cxf).
      unfold ndv, tv_vt. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_vt _ E_hvt rho tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hvt rho tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [exact (room_vt_holds rho HF1) | exact HF1]. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_vt HF CLN HTK HZ). unfold tv_vt. apply in_or_app. left. exact lines_in_kept_vt. }
  intros Hdnz.

  unfold ndv, tv_vt.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_vt CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HVT.Pre_vt (ndh h0 true HVT.nd0) PDk_vt NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHVT eq_refl
           E_vt s_vt R_vt Xk_vt rho tp kept_vt passed_vt frL bd_vt brest_vt (AHead pH true) (FAM (efmeasA (E_hvt, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_vt rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_vt frL rho' HK lines_in_kept_vt Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof avt_checks_nd as (Cndo & Cndf & CTo & CTf). pose proof avt_checks_back as (Bo & Bf & Tio & Tif & Rwf & Rsd & Rnx & RT & Rfb).
    cbn [PDk_vt liftPD PDh HVT.Posts_vt map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_vt_f) T_vt_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vt_f) (xfb_vt T_vt_f0) rho' T_vt_f0 B_vt_f tp' w Bf Hw). }
      apply (CUTV T_vt_f nd_vt_f 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvt T_vt_f ndA1 nd_vt_f 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_vt_ok) T_vt_ok rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb |].
        - apply (SPA_restate segs (JAv nd_vt_ok) rho' T_vt_ok1 S_vt_okR tp' w _ _ Rwf Rsd Rnx).
          + constructor; [|constructor]. cbn [fst snd]. apply sll1_add2_eq.
          + constructor.
          + rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vt_ok) (xfb_vt T_vt_ok0) rho' T_vt_ok0 B_vt_ok tp' w Bo Hw).
        -
          intros tr md _ HF1. pose proof avt_checks3 as (M1 & M2 & M3 & M4 & M5 & M6).
          pose proof (holds_mem _ _ _ HF1 M1) as F1. pose proof (holds_mem _ _ _ HF1 M2) as F2. pose proof (holds_mem _ _ _ HF1 M3) as F3. pose proof (holds_mem _ _ _ HF1 M4) as F4.
          pose proof (holds_mem _ _ _ HF1 M5) as F5. pose proof (holds_mem _ _ _ HF1 M6) as F6.
          rewrite h_ule in F1, F2, F3, F4, F5, F6. rewrite uval_lit in F4, F5, F6 by lia.
          pose proof (uval_range rho' pPOS) as RP. pose proof (uval_range rho' pLNL) as RL. pose proof (uval_range rho' c_avt) as RC. pose proof (uval_range rho' pNX) as RN.
          rewrite uval_add_small in F3 by lia.
          apply Forall_app. split; [|exact HF1]. constructor; [|constructor]. unfold rate_t1, t1, pE0. apply (proj2 (h_ule _ _ _)).
          rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
          rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
      apply TR_facts. intros HFo. pose proof avt_checks_pay as (PP1 & PP2 & PPay & _ & _ & _).
      apply (TR_pre (SPA segs (JAv nd_vt_okX) T_vt_ok rho' tp')).
      { intros w Hw. unfold nd_vt_okX, nd_vt_ok in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vt_ok frL (AHead pH true) bd_vt_ok comm_vt Xs_vt Ys_vt bdX_vt _ T_vt_ok rho' tp' w PP1 PP2 HFo PPay Hw). }
      apply (CUTV T_vt_ok nd_vt_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvt T_vt_ok ndA1 nd_vt_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S26SdVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S76SdS75VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S11S4S28Q40A1A1M0G0S2eSdVok;S29SdVJAFv;S34S48A2S6aR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S11S4S28Q40A1A1M0G0S2eSdVok;S29SdVJAFv;S34S49A2S6bR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHVT_T : ltac2:(tb__ "0|1|
S4S2S0S0A2M0A1S4S2G0S0A2A1S6dS11S4S28Q40A1A1S6cZ5R3A2S2eSdVok;S29SdS1dVAInv;VCST;VXGL;VKc;S32VCST;R6R5A3R6R5R4S1cS6fS50S6S66A3AaS65R3R2A5S5cSdS64R3R2S70VAInv;VCST;VXGL;VKc;S32VCST;A1S1cS52R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vt.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_vt CST) PTrue HVT.Pre_vt (ndh h0 true HVT.nd0) (PDh HVT.Posts_vt h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_vt CST) PTrue HVT.Pre_vt HVT.nd0 HVT.Posts_vt NPH h0 true h0_ltH HamC_vt HamPD_vt (P0_vt_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vt_sum AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SeS1bS5S2S0S12A2M0S11S4S28Q40A1A1M1S0G1S33S2S2S2SeS1bA2M2S5A2M3G0A2S3G3G0S3G2S5S3SeS1bR8R7A4R6A4R5A4S68A3S37S4fR7R5A3S30S3aZ0S36S3G3G0S3G2S5S3SeS1bRaR9A4R8A4R7A4R6A2M4A2S3bG4R4A2A2S2eSdVok;S29SdVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsT2) (map efdrop exitsT2) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertT_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsT2 exitsT In app] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
Qed.

Theorem arm_vt_T : ltac2:(tb__ "0|1|
S11S4S28Q40A1A1M0G0S2eSdVok;S29SdVJAFv;S34S44A2S4aR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vt (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHVT_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S77SdS75VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
S0S4S28Q40A1A1S2cF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S0S0S4S28Q40A1A1S2fS3aR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0S2dSdS29SdVJAFv;S34S48A2S6aR3R2A5VFAM;S36S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS6aS48A4U1A4S3S0S12S45S46Z1S47A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0S2dSdS29SdVJAFv;S34S49A2S6bR3R2A5VFAM;S36S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS6bS49A4U1A4S3S0S12S45S46Z1S47A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHVT_E : ltac2:(tb__ "0|1|
S4S2S0S0A2M0A1S4S2G0S0A2A1S6dS11S4S28Q40A1A1S6cZ5R3A2S2dSdS29SdS1dVAInv;VCST;VXGL;VKc;S32VCST;R6R5A3R6R5R4S1cS6fS50S6S66A3AaS65R3R2A5S5cSdS64R3R2S70VAInv;VCST;VXGL;VKc;S32VCST;A1S1cS52R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vt.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_vt CST) PTrue HVT.Pre_vt (ndh h0 true HVT.nd0) (PDh HVT.Posts_vt h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_vt CST) PTrue HVT.Pre_vt HVT.nd0 HVT.Posts_vt NPH h0 true h0_ltH HamC_vt HamPD_vt (P0_vt_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vt_sum_ex AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SeS1bS5S2S0S12A2M0S11S4S28Q40A1A1M1S0G1S33S2S2S2SeS1bA2M2S5A2M3G0A2S3G3G0S3G2S5S3SeS1bR8R7A4R6A4R5A4S68A3S37S4fR7R5A3S30S3aZ0S36S3G3G0S3G2S5S3SeS1bRaR9A4R8A4R7A4R6A2M4A2S3bG4R4A2A2S2dSdS29SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsT2 exitsT2 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertT_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsT2 exitsT In app] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
Qed.

Theorem arm_vt_E : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0S2dSdS29SdVJAFv;S34S44A2S4aR3R2A5VFAM;S36S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS4aS44A4U1A4S3S0S12S45S46Z11S47A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vt (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHVT_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
