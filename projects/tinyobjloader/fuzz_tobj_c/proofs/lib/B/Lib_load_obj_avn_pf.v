(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_handle_vn_pf"; "P0_hvn"; "PD_hvn"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "kept_vn"; "PDk_vn"; "cutsV"; "h0"; "R_vn"; "E_vn"; "Xk_vn"; "passed_vn"; "room_vn"; "s_vn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn.HVN"; "Pre_hvn"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "X_latchE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn_eqs"; "E_vn1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_handle_vn_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_avn_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S3cS0S2ScA1M0S11OF_;M1A2M2G2S37S5G0G1R1A3S6G0G1R1A3A2Lp;S4bA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_lt : (h0 < NF)%positive. Proof. reflexivity. Qed.
Lemma HamC_vn : nd_am HVN.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vn : ltac2:(tb__ "0|1|
S3cS0SeS18A2M0G0S2eS1eS22S6SeS18R1A3A1S1bA3Ld;S30A3"). Proof. repeat constructor. Qed.
Lemma P0_hvn_mono : ltac2:(tb__ "0|2|
S2S0SbSbA2M0A1M1G1G1S2S0G0SbA2A1S11G0S31G0R1R5A3S31G0R2R5A3F_;Fbn;S2fR6R5R3R2A4S2fR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS (A & B & C & D & E). split; [|split; [exact B | split; [exact C | split; [exact D | exact E]]]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma room_vn_holds : ltac2:(tb__ "0|0|
S11S3cS14S13R1A1S15SfS74A1A1A3S13R2S54A2F_;Frho;").
Proof.
  intros rho HF. pose proof avn_checks2 as (_ & _ & _ & _ & _ & _ & _ & CL & _ & _ & CC & CN & _).
  pose proof (holds_mem _ _ _ HF CL) as FL. pose proof (holds_mem _ _ _ HF CC) as FC. pose proof (holds_mem _ _ _ HF CN) as FN.
  rewrite h_ule in FL, FC, FN. rewrite uval_lit in FL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho c_avn) as RC.
  rewrite uval_add_small in FN by (rewrite uval_lit by lia; lia). rewrite uval_lit in FN by lia.
  rewrite uval_mul_lit in FC by lia.
  assert (E1 : uval rho (SAlu ALU_ADD c_avn (SLit 3)) = uval rho c_avn + 3) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
  assert (E2 : uval rho (SMd M_MUL (SLit 4) (SAlu ALU_ADD c_avn (SLit 3))) = 4 * (uval rho c_avn + 3)) by (rewrite uval_mul_lit by (rewrite ?E1; lia); rewrite E1; reflexivity).
  unfold room_vn. rewrite h_ule, E2. rewrite uval_lit by (unfold B_EW, Lib_vec_reserve.B_EW; lia).
  apply (room4_arith (uval rho c_avn) (uval rho pNX) (uval rho vLEN) 3); lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S70S11S2S25Q40A1A1S3eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S6fSdVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SbS5bVCST;R1A2S2dS38Z0R2A2S39R2S6bA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SbS5bVXGL;R1A2S2dS38Z0R2A2S39R2S6bA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SbS73R1A1S5bVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S0S0SbSbA2SbA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF0 : ltac2:(tb__ "0|1|
S2eS3S7fZ0S3dS0S0SbSbA2M0SbA2G0S5G0SbA2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S75VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1cVAInv;VCST;VXGL;S60VKc;Vrho0;VP0;VFB;VFF;VBX;S19Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S36VAInv;VCST;VXGL;S60VKc;Vrho0;VP0;VFB;VFF;VBX;S19VPhi;Vnd;Ad").

Lemma HXpow : ltac2:(tb__ "0|0|
SbS2dS38S68R1A2S39R1S3aS68Zb8A2A2A2S5bVXGL;R2A2F_;Fa;").
Proof.
  intros a Ha. apply HXlits. apply (in_litsL_In _ 145856 184 a); [|unfold pow10_tab, ScanDoubleAddr.pow10_tab in Ha; cbn in Ha |- *; lia].
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.X_lits. cbn [In]. do 17 right. left. reflexivity.
Qed.

Lemma HIN_vn : ltac2:(tb__ "0|1|
S11S4aS70S11S2S25Q40A1A1S3eS3cS14S13R6A1S15SfS51A1A1A3VP0;Vrho0;A1S69S60Vrho0;R8A3VAInv;R7R6R5R4A4S1dVrho0;R8A2S77RbS72S71R9A1A1A2S1fVFB;RaA2S20VFF;RbA2S24VFB;RcReS8S0S12S12A2S4cS53A3M0A4S78RfG0A2S79R10G0A2S21VFF;RfR11S33A4S2dS7dVCST;Vrho0;VFB;VFF;R12S4cS33S50A8S2dS7eVCST;VXGL;Vrho0;VFB;VFF;R12S4cS33S52A9S2fVCST;S76VFB;R12S4cA3S7cVFF;R12S33A3S48S47R12S50R11A3S55A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof avn_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_vn) by (apply (tvinA_sublist FB Ai rho (kept_vn ++ passed_vn)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vn) by (exact (tvd_app_l rho kept_vn passed_vn HD)).
  assert (HZk : tvz rho kept_vn) by (apply (tvz_sublist rho (kept_vn ++ passed_vn)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_vn frL extra_vn R_vn rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_vn in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_vn frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_vn frL o a HF CLN HT0 HZk lines_in_kept HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_vn frL xextraLO Xk_vn rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_vn frL r a Hav HP0 HE Ha).
  -
    pose proof avn_checks as (_ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_hvn. rewrite !rw_call'.
    change (wsub_get s_vn 15) with vBUF. change (wsub_get s_vn 18) with vLEN. change (wsub_get s_vn 12) with bA. change (wsub_get s_vn 58) with alA.
    change (wsub_get s_vn 56) with k_avn. change (wsub_get s_vn 54) with d_avn.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [|split; [|split; [|split]]].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_vn rho R_vn ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho kept_vn) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_vn) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + fact HF (SPUle k_avn (SLit 4294967295)) HkB. rewrite h_ule, uval_lit in HkB by lia.
      intros Hk. apply (tvz_in_kd rho (kept_vn ++ passed_vn) d_avn 4 k_avn HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32, Lib_vec_reserve.B32; lia | exact Hk].
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF0. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SbS2S25Q40A1A1S29F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S27SeS11S2S25Q40A1A1S29S3cS14S13R3A1S15SfR4A1A1A3VTR;S26SdR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S29S29S29S2cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S29OS29S2cR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S27S27SeSeS49S2S17A1M0S2S0SeS57A2M1A1S2S0S12S12A2M2A1S29S11S2S25Q40A1A1M3G2S31G2R1R5A3S31G2R2S10RbA1A3F_;Fr;S2eSaG0A1S5aRaR9R8A3S7G0R7A2A3S2eS9S59RbRaR9R8S3dG1SeS5SeS57A2R7A4A5S4A3S11G3VTR;S26SdRfRdR2R1A5S56SdS16SfRdA1A1R2R1RaA5A2Ftp1;Frho1;S2S3fA1M4S4aS3eS28SdR9R8R10S1G4S5cR3S5dR2R1A2A4A5R13RaR9R4R2A4R13S48S47RbRfS3bR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SeS57G4S4aS3eS11G3G4S4aS3eS31G1S1SeS57RaR9A4R14A3S28SdR12R11R19S1G4S5cR9S5dR8R7A2A4A5R1cR13R12RaR8A4S69S16SfR1aA1A1S48S47R14R18S3bR9R13RaA3A3R19A2R8A3S28SdR9R8ReS1G4S5cR7S5dR6R5A2A4A5ReS48S47R16R1aS3bRbR15RcA3A3R1bA2R15RaR9R8R6A6S2dS7aR17S3bRcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S6aR18S3bRdR17ReA3R1cR1dSfR1eA1SfR1fA1SfR11A1R1RcA9VTR;S26SdS58R11S48S47R19R1dS3bReR18RfA3A3R1eA2R18RdRcA5S7bR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S26SdR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S18SeS11S2S25Q40A1A1S29R6R3A1VTR;S26SdVJAv;R6A1R5R4R3A5R2A2F_;VTR;S26SdVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CHVN : ltac2:(tb__ "0|1|
S2S0SbSbA2M0A1S2S0G0SbA2A1S65S11S2S25Q40A1A1S64Z5R3A2VTR;S26SdS1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S66S4fS4S5fA3AaS5eR3R2A5S56SdS63R3R2S67VAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4dR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CUTV : ltac2:(tb__ "0|5|
SeS18S3S0SbS12A2M0S11S2S25Q40A1A1M1SbG1S31S0S0S0SeS18A2M2S3A2M3G0A2S1G3G0S1G2S3S1SeS18R8R7A4R6A4R5A4S4eA3S35S4bR7R5A3S2dS38Z0S34S1G3G0S1G2S3S1SeS18RaR9A4R8A4R7A4R6A2M4A2S39G4R4A2A2VTR;S26SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_vn : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0VTR;S26SdVJAFv;S32S40A2S46R3R2A5VFAM;S34S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S46S40A4U1A4S1SbS12S41S42Z11S43A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof avn_checks as (Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & Cpay & Cnb & Cbr).
  pose proof avn_checks2 as (_ & _ & CLN & _ & Cnp & Cnx & ClcL & CL26 & CiC & _ & _ & _ & Cfb).
  set (ndv := NDA tv_vn frL bd_vn (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_vn rho tp)).
  { intros w Hw. rewrite <- E_vn_eq. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_vn rho E_hvn E_vn1 tp w E_vn1_ok).
      unfold ndv, tv_vn. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_vn _ E_hvn rho tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hvn rho tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. constructor; [exact (room_vn_holds rho HF1) | constructor]. }
  apply TR_facts. intros HF.

  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_vn HF CLN HTK HZ). unfold tv_vn. apply in_or_app. left. exact lines_in_kept. }
  intros Hdnz.

  unfold ndv, tv_vn.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_hvn CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HVN.Pre_hvn (ndh h0 true HVN.nd0) PDk_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHVN eq_refl
           E_vn s_vn R_vn Xk_vn rho tp kept_vn passed_vn frL bd_vn brest_vn (AHead pH true) (FAM (efmeasA (E_hvn, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_vn rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_vn frL rho' HK lines_in_kept Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    cbn [PDk_vn liftPD PDh PD_hvn map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite T_vn_ok0_eq, nd_vn_ok_eq.
      apply (TR_pre (SPA segs (JAv nd_vn_ok) T_vn_ok rho' tp')).
      { intros w Hw. rewrite <- T_vn_ok_eq. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vn_ok) (xfb T_vn_ok0) rho' T_vn_ok0 B_vn_ok tp' w B_vn_ok_ok Hw). }
      apply (CUTV T_vn_ok nd_vn_ok 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvn T_vn_ok ndA1 nd_vn_ok 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite T_vn_f0_eq, nd_vn_f_eq.
      apply (TR_pre (SPA segs (JAv nd_vn_f) T_vn_f rho' tp')).
      { intros w Hw. rewrite <- T_vn_f_eq. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vn_f) (xfb T_vn_f0) rho' T_vn_f0 B_vn_f tp' w B_vn_f_ok Hw). }
      apply (CUTV T_vn_f nd_vn_f 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvn T_vn_f ndA1 nd_vn_f 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S23SdVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S6dSdS6cVAInv;VCST;VXGL;A5").

Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S11S2S25Q40A1A1M0G0S2bSdVok;S26SdVJAFv;S32S44A2S61R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE : ltac2:(tb__ "0|1|
S11S2S25Q40A1A1M0G0S2bSdVok;S26SdVJAFv;S32S45A2S62R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHVN_T : ltac2:(tb__ "0|1|
S2S0SbSbA2M0A1S2S0G0SbA2A1S65S11S2S25Q40A1A1S64Z5R3A2S2bSdVok;S26SdS1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S66S4fS4S5fA3AaS5eR3R2A5S56SdS63R3R2S67VAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4dR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vn.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_hvn CST) PTrue HVN.Pre_hvn (ndh h0 true HVN.nd0) (PDh PD_hvn h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_hvn CST) PTrue HVN.Pre_hvn HVN.nd0 PD_hvn NF h0 true h0_lt HamC_vn HamPD_vn (P0_hvn_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vn_sum AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SeS18S3S0SbS12A2M0S11S2S25Q40A1A1M1SbG1S31S0S0S0SeS18A2M2S3A2M3G0A2S1G3G0S1G2S3S1SeS18R8R7A4R6A4R5A4S4eA3S35S4bR7R5A3S2dS38Z0S34S1G3G0S1G2S3S1SeS18RaR9A4R8A4R7A4R6A2M4A2S39G4R4A2A2S2bSdVok;S26SdVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertV_ok 200%nat cps_arm NP cutsV exitsV ok (FAMQ tp0') Hok
           ecertV_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsV In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
Qed.

Theorem arm_vn_T : ltac2:(tb__ "0|1|
S11S2S25Q40A1A1M0G0S2bSdVok;S26SdVJAFv;S32S40A2S46R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vn (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHVN_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6eSdS6cVAInv;VCST;VXGL;A5").

Variable FAM : ltac2:(tb__ "0|0|
SbS2S25Q40A1A1S29F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SbSbS2S25Q40A1A1S2cS38R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0S2aSdS26SdVJAFv;S32S44A2S61R3R2A5VFAM;S34S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S61S44A4U1A4S1SbS12S41S42Z1S43A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0S2aSdS26SdVJAFv;S32S45A2S62R3R2A5VFAM;S34S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S62S45A4U1A4S1SbS12S41S42Z1S43A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHVN_E : ltac2:(tb__ "0|1|
S2S0SbSbA2M0A1S2S0G0SbA2A1S65S11S2S25Q40A1A1S64Z5R3A2S2aSdS26SdS1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S66S4fS4S5fA3AaS5eR3R2A5S56SdS63R3R2S67VAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4dR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vn.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_hvn CST) PTrue HVN.Pre_hvn (ndh h0 true HVN.nd0) (PDh PD_hvn h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_hvn CST) PTrue HVN.Pre_hvn HVN.nd0 PD_hvn NF h0 true h0_lt HamC_vn HamPD_vn (P0_hvn_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vn_sum_ex AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SeS18S3S0SbS12A2M0S11S2S25Q40A1A1M1SbG1S31S0S0S0SeS18A2M2S3A2M3G0A2S1G3G0S1G2S3S1SeS18R8R7A4R6A4R5A4S4eA3S35S4bR7R5A3S2dS38Z0S34S1G3G0S1G2S3S1SeS18RaR9A4R8A4R7A4R6A2M4A2S39G4R4A2A2S2aSdS26SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertV_ok 200%nat cps_arm NP cutsV exitsV (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertV_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsV In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
Qed.

Theorem arm_vn_E : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0S2aSdS26SdVJAFv;S32S40A2S46R3R2A5VFAM;S34S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S46S40A4U1A4S1SbS12S41S42Z11S43A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vn (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHVN_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
