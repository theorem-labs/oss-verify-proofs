(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "nil"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_handle_mtllib_pf"; "P0_ml"; "@Corelib.Init.Logic"; "and"; "eq"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aml.HML"; "Pre_ml"; "nd0"; "Posts_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aml"; "PDk_ml"; "cutsM"; "R_ml"; "E_ml"; "Xk_ml"; "s_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vCFGp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface";
"in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_handle_mtllib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_handle_mtllib_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_aml.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HMLAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S48S0S2SdA1M0S12OF_;M1A2M2G2S38S5G0G1R1A3S6G0G1R1A3A2Lp;S4bA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_ml : nd_am HML.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_ml : ltac2:(tb__ "0|1|
S48S0SfS19A2M0G0S30S1fS23S6SfS19R1A3A1S1cA3Ld;S57A3"). Proof. repeat constructor. Qed.
Lemma P0_ml_mono : ltac2:(tb__ "0|2|
S2S0ScScA2M0A1M1G1G1S2S0G0ScA2A1S12G0S31G0R1R5A3S31G0R2R5A3F_;Fbn;S2eR6R5R3R2A4S2eR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & D & E). split; [|split; [exact D | exact E]]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S6fS12S2S26Q40A1A1S3cOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S6eSeVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
ScS67VCST;R1A2S2fS3aZ0R2A2S3bR2S6aA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
ScS67VXGL;R1A2S2fS3aZ0R2A2S3bR2S6aA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
ScS72R1A1S67VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S0S0ScScA2ScA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF1 : ltac2:(tb__ "0|1|
S30S3S7eZ1S49S0S0ScScA2M0ScA2G0S5G0ScA2VFF;A4A2U0A3").
Hypothesis HCFG : ltac2:(tb__ "0|0|
S7aVFF;S64Vrho0;S5fA2Z90A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S12OFr;") := ltac2:(tb__ "0|0|
S73VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1dVAInv;VCST;VXGL;S5eVKc;Vrho0;VP0;VFB;VFF;VBX;S1aVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S37VAInv;VCST;VXGL;S5eVKc;Vrho0;VP0;VFB;VFF;VBX;S1aVPhi;Vnd;Ad").

Lemma HIN_ml : ltac2:(tb__ "0|2|
S12S4aS6fS12S2S26Q40A1A1S3cS48S15S14R6A1S16S10S5bA1A1A3VP0;Vrho0;A1S68S5eVrho0;R8A3VAInv;R7R6R5R4A4S1eVrho0;R8A2S75RbS71S70R9A1A1A2S20VFB;RaA2S21VFF;RbA2S25VFB;RcReS8S0S13S13A2M0S34SaG0A1A3M1A4S76RfG1A2S77R10G1A2S22VFF;RfR11S33A4S2fS7cVCST;Vrho0;VFB;VFF;R12S34S33S5aA8S2fS7dVCST;VXGL;Vrho0;VFB;VFF;R12S34S33S5cA9S2eVCST;S74VFB;R12S34A3S7bVFF;R12S33A3S46S45R12S5aR11A3S5dA2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. rewrite app_nil_r in HN, HD, HZ.
  pose proof aml_checks as (_ & _ & _ & Cta & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tvL frL extra_ml R_ml rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
    intros o a Ho HE Hr. unfold extra_ml in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho tvL frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ tvL frL o a HF CLN HT0 HZ lines_in_tvL HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tvL frL xextraLO Xk_ml rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho tvL frL r a Hav HP0 HE Ha).
  - destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_ml, P0_builder. rewrite !rw_call'.
    change (wsub_get s_ml 15) with vBUF. change (wsub_get s_ml 18) with vLEN. change (wsub_get s_ml 12) with bA. change (wsub_get s_ml 58) with alA.
    change (wsub_get s_ml 109) with vCFGp.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|split].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_ml rho R_ml ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho tvL) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho tvL) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + destruct HCFG as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      rewrite (AG 15%positive vCFGp eq_refl ltac:(reflexivity)). lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF1. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
ScS2S26Q40A1A1S2aF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S28SfS12S2S26Q40A1A1S2aS48S15S14R3A1S16S10R4A1A1A3VTR;S27SeR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2aS2aS2aS2dR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2aOS2aS2dR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S28S28SfSfS47S2S18A1M0S2S0SfS4eA2M1A1S2S0S13S13A2M2A1S2aS12S2S26Q40A1A1M3G2S31G2R1R5A3S31G2R2S11RbA1A3F_;Fr;S30SbG0A1S51RaR9R8A3S7G0R7A2A3S30S9S50RbRaR9R8S49G1SfS5SfS4eA2R7A4A5S4A3S12G3VTR;S27SeRfRdR2R1A5S4dSeS17S10RdA1A1R2R1RaA5A2Ftp1;Frho1;S2S3dA1M4S4aS3cS29SeR9R8R10S1G4S52R3S53R2R1A2A4A5R13RaR9R4R2A4R13S46S45RbRfS39R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SfS4eG4S4aS3cS12G3G4S4aS3cS31G1S1SfS4eRaR9A4R14A3S29SeR12R11R19S1G4S52R9S53R8R7A2A4A5R1cR13R12RaR8A4S68S17S10R1aA1A1S46S45R14R18S39R9R13RaA3A3R19A2R8A3S29SeR9R8ReS1G4S52R7S53R6R5A2A4A5ReS46S45R16R1aS39RbR15RcA3A3R1bA2R15RaR9R8R6A6S2fS78R17S39RcR16RdA3R1bR1cR1dR10R1eR19RbA9S12S69R18S39RdR17ReA3R1cR1dS10R1eA1S10R1fA1S10R11A1R1RcA9VTR;S27SeS4fR11S46S45R19R1dS39ReR18RfA3A3R1eA2R18RdRcA5S79R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S27SeR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S12OF_;S19SfS12S2S26Q40A1A1S2aR6R3A1VTR;S27SeVJAv;R6A1R5R4R3A5R2A2F_;VTR;S27SeVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHML : ltac2:(tb__ "0|1|
S2S0ScScA2M0A1S2S0G0ScA2A1S63S12S2S26Q40A1A1S62Z5R3A2VTR;S27SeS1bVAInv;VCST;VXGL;VKc;S2eVCST;R6R5A3R6R5R4S1aS65S4cS4S56A3AaS55R3R2A5S4dSeS54R3R2S66VAInv;VCST;VXGL;VKc;S2eVCST;A1S1aS58R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
SfS19S3S0ScS13A2M0S12S2S26Q40A1A1M1ScG1S31S0S0S0SfS19A2M2S3A2M3G0A2S1G3G0S1G2S3S1SfS19R8R7A4R6A4R5A4S59A3S36S4bR7R5A3S2fS3aZ0S35S1G3G0S1G2S3S1SfS19RaR9A4R8A4R7A4R6A2M4A2S3bG4R4A2A2VTR;S27SeVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_ml : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0VTR;S27SeVJAFv;S32S3eA2S44R3R2A5VFAM;S35S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S44S3eA4U1A4S1ScS13S3fS40Z11S41A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof aml_checks as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cxk & Chand & Cpay & Cnb & Cbr & Cnp & Cnx & _ & _ & CLN).

  apply (TR_pre (SPA segs (JAv (NDA (tvL ++ []) frL (bdA A1) (AHead pH true))) E_ml rho tp)).
  { intros w Hw. rewrite app_nil_r. exact (SPA_axforms segs (JAv ndA1) xf_ml rho E_hm E_ml tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv] in HZ. rewrite app_nil_r in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    exact (lines_nz rho _ (topG (aa_geom Ai)) tvL HF CLN HTK HZ lines_in_tvL). }
  intros Hdnz.

  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_ml CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HML.Pre_ml (ndh h0 true HML.nd0) PDk_ml NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHML eq_refl
           E_ml s_ml R_ml Xk_ml rho tp tvL [] frL (bdA A1) (bdA A1) (AHead pH true) (FAM (efmeasA (E_hm, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_ml rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho tvL frL rho' HK lines_in_tvL Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof aml_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif).
    cbn [PDk_ml liftPD PDh HML.Posts_ml map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf. rewrite app_nil_r. fold ndL ndA1. change (NDA tvL frL (bdA A1) (AHead pH true)) with ndA1.
      apply (TR_pre (SPA segs (JAv ndA1) T_ml_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_ml T_ml_f0) rho' T_ml_f0 B_ml_f tp' w Bf Hw). }
      apply (CUTV T_ml_f ndA1 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hm T_ml_f ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo. rewrite app_nil_r. change (NDA tvL frL (bdA A1) (AHead pH true)) with ndA1.
      apply (TR_pre (SPA segs (JAv ndA1) T_ml_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_ml T_ml_ok0) rho' T_ml_ok0 B_ml_ok tp' w Bo Hw). }
      apply (CUTV T_ml_ok ndA1 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hm T_ml_ok ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S24SeVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S6cSeS6bVAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S12S2S26Q40A1A1M0G0S2cSeVok;S27SeVJAFv;S32S42A2S60R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S12S2S26Q40A1A1M0G0S2cSeVok;S27SeVJAFv;S32S43A2S61R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHML_T : ltac2:(tb__ "0|1|
S2S0ScScA2M0A1S2S0G0ScA2A1S63S12S2S26Q40A1A1S62Z5R3A2S2cSeVok;S27SeS1bVAInv;VCST;VXGL;VKc;S2eVCST;R6R5A3R6R5R4S1aS65S4cS4S56A3AaS55R3R2A5S4dSeS54R3R2S66VAInv;VCST;VXGL;VKc;S2eVCST;A1S1aS58R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_ml.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_ml CST) PTrue HML.Pre_ml (ndh h0 true HML.nd0) (PDh HML.Posts_ml h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_ml CST) PTrue HML.Pre_ml HML.nd0 HML.Posts_ml NPH h0 true h0_ltH HamC_ml HamPD_ml (P0_ml_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_mtllib_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SfS19S3S0ScS13A2M0S12S2S26Q40A1A1M1ScG1S31S0S0S0SfS19A2M2S3A2M3G0A2S1G3G0S1G2S3S1SfS19R8R7A4R6A4R5A4S59A3S36S4bR7R5A3S2fS3aZ0S35S1G3G0S1G2S3S1SfS19RaR9A4R8A4R7A4R6A2M4A2S3bG4R4A2A2S2cSeVok;S27SeVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsM) (map efdrop exitsM) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertM_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsM In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
Qed.

Theorem arm_ml_T : ltac2:(tb__ "0|1|
S12S2S26Q40A1A1M0G0S2cSeVok;S27SeVJAFv;S32S3eA2S44R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_ml (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHML_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6dSeS6bVAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
ScS2S26Q40A1A1S2aF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
ScScS2S26Q40A1A1S2dS3aR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0S2bSeS27SeVJAFv;S32S42A2S60R3R2A5VFAM;S35S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S60S42A4U1A4S1ScS13S3fS40Z1S41A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0S2bSeS27SeVJAFv;S32S43A2S61R3R2A5VFAM;S35S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S61S43A4U1A4S1ScS13S3fS40Z1S41A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHML_E : ltac2:(tb__ "0|1|
S2S0ScScA2M0A1S2S0G0ScA2A1S63S12S2S26Q40A1A1S62Z5R3A2S2bSeS27SeS1bVAInv;VCST;VXGL;VKc;S2eVCST;R6R5A3R6R5R4S1aS65S4cS4S56A3AaS55R3R2A5S4dSeS54R3R2S66VAInv;VCST;VXGL;VKc;S2eVCST;A1S1aS58R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_ml.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_ml CST) PTrue HML.Pre_ml (ndh h0 true HML.nd0) (PDh HML.Posts_ml h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_ml CST) PTrue HML.Pre_ml HML.nd0 HML.Posts_ml NPH h0 true h0_ltH HamC_ml HamPD_ml (P0_ml_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_mtllib_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SfS19S3S0ScS13A2M0S12S2S26Q40A1A1M1ScG1S31S0S0S0SfS19A2M2S3A2M3G0A2S1G3G0S1G2S3S1SfS19R8R7A4R6A4R5A4S59A3S36S4bR7R5A3S2fS3aZ0S35S1G3G0S1G2S3S1SfS19RaR9A4R8A4R7A4R6A2M4A2S3bG4R4A2A2S2bSeS27SeVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsM exitsM (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertM_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsM In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
Qed.

Theorem arm_ml_E : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0S2bSeS27SeVJAFv;S32S3eA2S44R3R2A5VFAM;S35S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S44S3eA4U1A4S1ScS13S3fS40Z11S41A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_ml (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHML_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
