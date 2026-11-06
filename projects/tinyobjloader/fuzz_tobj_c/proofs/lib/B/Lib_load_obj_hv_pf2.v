(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "list"; "bool"; "true"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA"; "frozen"; "nd_below"; "ok_frameKA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "sprop"; "sprop_below"; "ss_next"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "E_hv0"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf1"; "pure_ruleL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "PhisH"; "mH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "V_B"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Posts_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "T_sd1n"; "T_sd1y"; "T_sd2n"; "T_sd2y"; "T_sd3n"; "T_sd3y"; "T_sd4n"; "T_sd4y"; "T_sd5n"; "T_sd5y"; "T_sd6n"; "T_sd6y"; "T_sd7n"; "T_sd7y"; "T_sd8n"; "T_sd8y"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv1e"; "cutsH1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv2"; "cutsH2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Posts_sd"; "Pre_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf2.Sum"; "fb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_build_line_index_rom_call.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hvpk Lib_load_obj_hv2 Lib_load_obj_hv1c Lib_load_obj_hv1e Lib_load_obj_hv_pf1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Lemma VB_meas : ltac2:(tb__ "0|0|
S13S26S8S36R1S31A2S9A3S25S54P1ccR2A2S54P1d3R2A2A2F_;Fn;").
Proof.
  intros n H. split; [apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto | apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto].
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S5cS14S7S1aQ40A1A1S56OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S53SbVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S12S38VCST;R1A2S25S2bZ0R2A2S2cR2S4fA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S12S38VXGL;R1A2S25S2bZ0R2A2S2cR2S4fA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S12S58R1A1S38VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S7S5S5S12S12A2S12A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S14OFr;") := ltac2:(tb__ "0|0|
S5bVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
SeVAInv;VCST;VXGL;S27VKc;Vrho0;VP0;VFB;VFF;VBX;SdVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S35VAInv;VCST;VXGL;S27VKc;Vrho0;VP0;VFB;VFF;VBX;SdVPhi;Vnd;Ad").
Let frozen_stable : ltac2:(tb__ "0|0|
S13S13ScS14S55S27R3A2S26S8S10R4R3A2S9A3S1cSbR6SfVAInv;VCST;VXGL;S27VKc;Vrho0;VP0;VFB;VFF;VBX;SdR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S57VAInv;VCST;VXGL;VALA;S27VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Lemma CXR_entry : ltac2:(tb__ "0|0|
S26S8S5aVXGL;S16S1S28A1A1S32Z4Z12S2S28A1A6S9A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition fb (T : axst) : bool := ltac2:(tb__ "0|1|
S2aS17S18S19S1VT;A1M0A1A1S16G0A1A3").
Lemma Cfb_sd : ltac2:(tb__ "0|0|
S26S8S2aS0S59S3S0S3bS3S0S3cS3S0S3dS3S0S3eS3S0S3fS3S0S40S3S0S41S3S0S42S3S0S43S3S0S44S3S0S45S3S0S46S3S0S47S3S0S48S3S0S49S3S0S4aSaS0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S9A3").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fb_in : ltac2:(tb__ "0|1|
S0S29S0R1S3S0S3bS3S0S3cS3S0S3dS3S0S3eS3S0S3fS3S0S40S3S0S41S3S0S42S3S0S43S3S0S44S3S0S45S3S0S46S3S0S47S3S0S48S3S0S49S3S0S4aSaS0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S26S8S2aS17S18S19S1R2A1M0A1A1S16G0A1A3S9A3F_;FT;").
Proof using . intros T H. exact (proj1 (forallb_forall _ _) Cfb_sd T H). Qed.
Ltac inl := cbn [In]; repeat (first [left; reflexivity | right]).

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S11SbVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S51SbS50VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XKVR : ltac2:(tb__ "0|1|
S14S7S1aQ40A1A1M0G0S22SbVok;S1bSbVJAFv;S30S1dA2S37R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma PURE_sd_T : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S22SbVok;A2S4eS4dAb").
Proof using ALA HKc Hok.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply scan_double_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma PURE_da_T : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S22SbVok;A2S3aS39Ab").
Proof using ALA HKc Hok.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.

Lemma CUT2_T : ltac2:(tb__ "0|4|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR7R6A4R5A4R4A4S4cA3S34S2eR6R4A3S22SbVok;S1bSbVJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKVR.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH2_ok 600%nat cps_v NP cutsH2 exitsH2 ok (FAMQ tp0') Hok
           ecertH2_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsH2 In] in HinX. destruct HinX as [E|[]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Lemma CUT1_T : ltac2:(tb__ "0|4|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR7R6A4R5A4R4A4S4bA3S34S2eR6R4A3S22SbVok;S1bSbVJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKVR.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH1_ok 600%nat cps_v NP cutsH1 exitsH1 ok (FAMQ tp0') Hok
           ecertH1_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  set (QQ := fun w => SPfamGTA segs (map (nodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) (map efdrop cutsH1)) w \/ FAMQ tp0' w).

  assert (SD : forall Es Tn Ty, sd_chk Es Tn Ty -> fb Tn = true -> fb Ty = true ->
               In (Tn, ndA1, 1%nat) (map efdrop cutsH1) -> In (Ty, ndA1, 1%nat) (map efdrop cutsH1) ->
               tblB rho1 -> triple segs ok (SPA segs (JAv ndA1) Es rho1 tp1) QQ).
  { intros Es Tn Ty Hchk Hbn Hby Hinn Hiny HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    apply (site_sd AInv CST XGL Kc FB FF BX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_sd_T Es Tn Ty rho1 tp1 QQ Hchk Hbn Hby).
    - intros rho' HF Hag. exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH1) Tn ndA1 1%nat (FAMQ tp0') rho' tp1 Hinn
                                   (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
    - intros rho' HF Hag. exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH1) Ty ndA1 1%nat (FAMQ tp0') rho' tp1 Hiny
                                   (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)). }

  assert (DA : forall E0 Ec T0 B Td, da_chk E0 Ec T0 B Td -> (exists rv, In (Td, ndA1, 1%nat, rv) cutsH2) ->
               tblB rho1 -> triple segs ok (SPA segs (JAv ndA1) E0 rho1 tp1) QQ).
  { intros E0 Ec T0 B Td Hchk [rvd Hind] HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    apply (site_da AInv CST XGL Kc FB FF BX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_da_T E0 Ec T0 B Td rho1 tp1 QQ Hchk).
    intros rho' HF Hag. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (CUT2_T Td ndA1 1%nat rvd rho' tp1 tp0' Hind (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)). }
  pose proof hv_checks_sd1 as [Cxf1 Csd1].
  assert (Hd1 : exists rv, In (T_da1, ndA1, 1%nat, rv) cutsH2) by (exists (mH 16 3); cbn [cutsH2]; inl).
  assert (Hd2 : exists rv, In (T_da2, ndA1, 1%nat, rv) cutsH2) by (exists (mH 16 3); cbn [cutsH2]; inl).
  assert (Hd3 : exists rv, In (T_da3, ndA1, 1%nat, rv) cutsH2) by (exists (mH 16 3); cbn [cutsH2]; inl).
  cbn [exitsH1 In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd];
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)); intros HP1.
  - apply (TRs_pre segs ok (SPA segs (JAv ndA1) E_sd1 rho1 tp1)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_sd1 rho1 E_sd1r E_sd1 tp1 w Cxf1 Hw). }
    exact (SD _ _ _ Csd1 (fb_in T_sd1n ltac:(inl)) (fb_in T_sd1y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd2 (fb_in T_sd2n ltac:(inl)) (fb_in T_sd2y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd3 (fb_in T_sd3n ltac:(inl)) (fb_in T_sd3y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd4 (fb_in T_sd4n ltac:(inl)) (fb_in T_sd4y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd5 (fb_in T_sd5n ltac:(inl)) (fb_in T_sd5y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd6 (fb_in T_sd6n ltac:(inl)) (fb_in T_sd6y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd7 (fb_in T_sd7n ltac:(inl)) (fb_in T_sd7y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd8 (fb_in T_sd8n ltac:(inl)) (fb_in T_sd8y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (DA E_da1 E_da1c T_da10 B_da1 T_da1 hv2_checks_da1 Hd1 HP1).
  - exact (DA E_da2 E_da2c T_da20 B_da2 T_da2 hv2_checks_da2 Hd2 HP1).
  - exact (DA E_da3 E_da3c T_da30 B_da3 T_da3 hv2_checks_da3 Hd3 HP1).
  - apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok ndA1 K_vr rho1 tp1 _ HP1).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Theorem arm_hv_T : ltac2:(tb__ "0|1|
S14S7S1aQ40A1A1M0G0S22SbVok;S1bSbVJAFv;S30S1dA2S28R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKVR.
  intros rho tp tp0.
  apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv_checks_entry as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
  apply (entry_hv AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) rho tp _ CXR_entry).
  intros rho' Hag.
  exact (CUT1_T K_hv0c ndA1 1%nat _ rho' tp tp0 ltac:(cbn [cutsH1]; inl) (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S52SbS50VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
S12S7S1aQ40A1A1S23F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S12S12S7S1aQ40A1A1S24S2bR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XKVR : ltac2:(tb__ "0|2|
S14S7S1aQ40A1A1M0G0S21SbS1bSbVJAFv;S30S1dA2S37R3R2A5VFAM;S33S4S5S5S0ScA2M1S6A2S5S12S15A2S4G1S6S4S0ScS37S1dA4U1A4S2fZfZ64A2A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma PURE_sd_E : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S21SbA1S4eS4dAb").
Proof using ALA HKc.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply scan_double_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma PURE_da_E : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S21SbA1S3aS39Ab").
Proof using ALA HKc.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.

Lemma CUT2_E : ltac2:(tb__ "0|5|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1S12G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR8R7A4R6A4R5A4S4cA3S34S2eR7R5A3S25S2bZ0S33S4G3G0S4G2S6S4S0ScRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S21SbS1bSbVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKVR.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH2_ok 600%nat cps_v NP cutsH2 exitsH2 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH2_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  cbn [exitsH2 In] in HinX. destruct HinX as [E|[]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Lemma CUT1_E : ltac2:(tb__ "0|5|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1S12G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR8R7A4R6A4R5A4S4bA3S34S2eR7R5A3S25S2bZ0S33S4G3G0S4G2S6S4S0ScRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S21SbS1bSbVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKVR.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH1_ok 600%nat cps_v NP cutsH1 exitsH1 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH1_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  set (FQ := fun (bb : Z) (w : world) => SPfamETA segs (map (enodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) cutsH1) bb w \/ FAM bb tp0' w).

  assert (SD : forall Es E0 Tn Ty aE aT, sd_chk Es Tn Ty -> fb Tn = true -> fb Ty = true -> 0 <= aT < aE -> aE < 2 ^ 27 ->
               In (Tn, ndA1, 1%nat, mH 16 aT) cutsH1 -> In (Ty, ndA1, 1%nat, mH 16 aT) cutsH1 ->
               tblB rho1 -> etriple segs (SPA segs (JAv ndA1) Es rho1 tp1) (FQ (efmeasA (E0, ndA1, 1%nat, mH 16 aE) rho1))).
  { intros Es E0 Tn Ty aE aT Hchk Hbn Hby Ha HaE Hinn Hiny HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & CL1 & CL2 & CL3).
    destruct (VB_meas _ CVB) as [L460 L467].
    apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho1 _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
    apply (site_sd AInv CST XGL Kc FB FF BX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_sd_E Es Tn Ty rho1 tp1 _ Hchk Hbn Hby).
    - intros rho' HF Hag.
      apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH1 Tn ndA1 1%nat (mH 16 aT) _ _ rho' tp1 Hinn (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
      apply (VLA_lt2 rho1 rho' 16 16 aE aT E0 Tn ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia].
    - intros rho' HF Hag.
      apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH1 Ty ndA1 1%nat (mH 16 aT) _ _ rho' tp1 Hiny (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
      apply (VLA_lt2 rho1 rho' 16 16 aE aT E0 Ty ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }

  assert (DA : forall E0 Ec T0 B Td, da_chk E0 Ec T0 B Td -> In (Td, ndA1, 1%nat, mH 16 3) cutsH2 ->
               tblB rho1 -> etriple segs (SPA segs (JAv ndA1) E0 rho1 tp1) (FQ (efmeasA (E0, ndA1, 1%nat, mH 16 4) rho1))).
  { intros E0 Ec T0 B Td Hchk Hind HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & CL1 & CL2 & CL3).
    destruct (VB_meas _ CVB) as [L460 L467].
    apply (site_da AInv CST XGL Kc FB FF BX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_da_E E0 Ec T0 B Td rho1 tp1 _ Hchk).
    intros rho' HF Hag. destruct (loopF_vals rho1 _ HF (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    apply (CUT2_E Td ndA1 1%nat (mH 16 3) rho' tp1 _ tp0' Hind (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
    apply (VLA_lt2 rho1 rho' 16 16 4 3 E0 Td ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  pose proof hv_checks_sd1 as [Cxf1 Csd1].
  cbn [exitsH1 In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-;
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)); intros HP1.
  - apply (TRe_pre segs (SPA segs (JAv ndA1) E_sd1 rho1 tp1)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_sd1 rho1 E_sd1r E_sd1 tp1 w Cxf1 Hw). }
    exact (SD E_sd1 E_sd1r T_sd1n T_sd1y 38 36 Csd1 (fb_in T_sd1n ltac:(inl)) (fb_in T_sd1y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd2 E_sd2 T_sd2n T_sd2y 34 32 hv_checks_sd2 (fb_in T_sd2n ltac:(inl)) (fb_in T_sd2y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd3 E_sd3 T_sd3n T_sd3y 30 28 hv_checks_sd3 (fb_in T_sd3n ltac:(inl)) (fb_in T_sd3y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd4 E_sd4 T_sd4n T_sd4y 26 24 hv_checks_sd4 (fb_in T_sd4n ltac:(inl)) (fb_in T_sd4y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd5 E_sd5 T_sd5n T_sd5y 22 20 hv_checks_sd5 (fb_in T_sd5n ltac:(inl)) (fb_in T_sd5y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd6 E_sd6 T_sd6n T_sd6y 18 16 hv_checks_sd6 (fb_in T_sd6n ltac:(inl)) (fb_in T_sd6y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd7 E_sd7 T_sd7n T_sd7y 14 12 hv_checks_sd7 (fb_in T_sd7n ltac:(inl)) (fb_in T_sd7y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd8 E_sd8 T_sd8n T_sd8y 10 8 hv_checks_sd8 (fb_in T_sd8n ltac:(inl)) (fb_in T_sd8y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (DA E_da1 E_da1c T_da10 B_da1 T_da1 hv2_checks_da1 ltac:(cbn [cutsH2]; inl) HP1).
  - exact (DA E_da2 E_da2c T_da20 B_da2 T_da2 hv2_checks_da2 ltac:(cbn [cutsH2]; inl) HP1).
  - exact (DA E_da3 E_da3c T_da30 B_da3 T_da3 hv2_checks_da3 ltac:(cbn [cutsH2]; inl) HP1).
  - apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndA1 K_vr rho1 tp1 _ HP1).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Theorem arm_hv_E : ltac2:(tb__ "0|2|
S14S7S1aQ40A1A1M0G0S21SbS1bSbVJAFv;S30S1dA2S28R3R2A5VFAM;S33S4S5S5S0ScA2M1S6A2S5S12S15A2S4G1S6S4S0ScS28S1dA4U1A4S4S12S15S1eS1fZ11S20A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKVR.
  intros rho tp tp0.
  apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv_checks_entry as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & CL1 & CL2 & CL3).
  destruct (VB_meas _ CVB) as [L460 L467].
  apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
  apply (entry_hv AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) rho tp _ CXR_entry).
  intros rho' Hag.
  apply (CUT1_E K_hv0c ndA1 1%nat (mH 16 40) rho' tp _ tp0 ltac:(cbn [cutsH1]; inl) (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI)).
  apply (VLA_lt2 rho rho' 17 16 0 40 E_hv0 K_hv0c ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | left; lia].
Qed.
End Existence.
End Sum.
