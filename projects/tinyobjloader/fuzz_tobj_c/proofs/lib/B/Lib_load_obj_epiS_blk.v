(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_facts"; "sprop"; "holds"; "ss_next"; "SLit"; "sobj"; "SVar"; "SPUle"; "SAlu"; "sprop_eqb"; "SPEq"; "agree_below"; "cell"; "odefault"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "g8"; "@Corelib.Init.Datatypes"; "true"; "list"; "bool"; "prod"; "app"; "pair"; "Some"; "fst"; "option"; "cons"; "nil"; "false"; "nat"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "s_vf"; "kept_ad"; "Xk_vf"; "xfb_vf"; "PDk_vf"; "xf_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "uval"; "bd_subst"; "BUD"; "BXok_d"; "bd_below"; "bd_wpos"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2.VF"; "Pre_vf"; "P_zero"; "P_zero2"; "nd0"; "tv_vf"; "P_fail"; "P_ok"; "CHv"; "am_vf"; "vHDn"; "vHDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "extraLO"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "add"; "lt"; "pow"; "mul"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "AHead"; "amode"; "am_subst"; "PTrue"; "JA"; "JAi"; "ndesc"; "nd_tv"; "tvinA"; "JA_pre"; "TPA"; "am_eqb"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "xLK"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "ldefR"; "V_ldR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub_get"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_defs"; "ldef_facts"; "nx500"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "FBx"; "tvz"; "T_ok"; "tv_sub_eqb"; "tvd";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "FFx"; "pdescA"; "pclMA"; "pd_okA"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2.VFP"; "P0_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "keptK"; "keptR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiS1 Lib_load_obj_epiS_kit Lib_load_obj_epiS2 Lib_load_obj_epiS_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_epiD_pf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DP. Include Lib_load_obj_epiD_pf. End DP.

Section Le2.
Variable segs' : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S7cS3S17S6aQ40A1A1S6dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S17S19S19S24S24A2S24A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Lemma BUD_le2 : ltac2:(tb__ "0|1|
S17S5A1S17S2cA1M0G0S19S24S24A2S24S24S24S3S6bS5S6R1A1R8A3S0S18S85R9R8R7A3S16A3S2fR8R7R6R5R4R3A6S2fRaR8R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;FBXv;Fbfrom;Fbto;Ffacts;").
Proof.
  intros facts bto bfrom BXv V Km Kf rho HF Hle H. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2).
  destruct (bud_le2_sound facts _ _ rho HF Hn Hle) as (L1 & L2 & L3 & L4 & L5).
  unfold BUD. repeat (split; [assumption|]). lia.
Qed.
Lemma JAi_le2 : ltac2:(tb__ "0|1|
S17S5A1S17S19S2S2A2A1S17S19S19S2S24A2S2A2A1S17S2cA1M0G0S58S7cS24S3S17S6aQ40A1A1S17S6eA1S6dS6bS5S6R4A1RcA3S0S18S85RdR9RaA3S16A3S5cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S56RdRcRbR9A4R8R7R6R5R4R3A12S5cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S56ReRdRbRaA4R9R8R7R6R5R4A12F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fam;Fbd';Fbd;Ffr;Ftv;Ffacts;").
Proof.
  intros facts tv fr bd bd' am Ai kc rho tp tr md HF Hle HJ.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|].
  split; [|split; [exact HPA | split; [exact HCK | exact HCN]]].
  exact (BUD_le2 facts bd' bd _ _ _ _ rho HF Hle HBU).
Qed.
Lemma SPA_JA_le2 : ltac2:(tb__ "0|1|
S17S19S2S2A2A1S17S19S19S2S24A2S2A2A1S17S2cA1M0G0S58S12S3S17S6aQ40A1A1S73S0S18S85S4S13R4A1A1R6R7A3S16A3S49Vsegs';S5bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S56RaR9R8R6A4AcR5R4R3R2A6S49Vsegs';S5bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S56RbRaR8R7A4AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd';Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd bd' am A rho tp [tr [ms md]] Hle [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  exact (JAi_le2 _ tv fr bd bd' am Ai kc rho tp tr md (smatchA_facts segs' _ _ _ _ Hsm) Hle HJ).
Qed.
End Le2.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S7cS3S17S6aQ40A1A1S6dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sb0S3fVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S24S9fVCST;R1A2S1S42Z0R2A2S45R2Sa5A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S24S9fVXGL;R1A2S1S42Z0R2A2S45R2Sa5A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S24Sa7R1A1S9fVXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S17S19S19S24S24A2S24A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
Sa8VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S5bVAInv;VCST;VXGL;S80VKc;Vrho0;VP0;VFB;VFF;VBX;S5aVnd;Ac").

Lemma block_pclMAL : ltac2:(tb__ "0|2|
S7cS3S17S19S2S2A2M0A1G0S24S5fVFB;R5R4R3A4S8fR5R4A2S4cG0R4R5A3S1S42S2dR7S1dS2S2R5A3A2M1R4A2S45R4S44G1S2dR7S23S2S2R5A3A2A2A2A2S3S96VCST;R1S8eVFB;R9R8A3S94VFF;R9S40A3R6A5Fr0;F_;F_;F_;F_;Fa;Ft;Fkept;Frho;FAi;").
Proof using .
  intros Ai rho kept t a HN HZ Hin Ha r0.
  destruct (Z.eq_dec (uval rho (fst t)) 0) as [Hz|Hnz].
  - exfalso. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [snd] in X.
    specialize (X ltac:(intros Y; apply Y; exact Hz)). unfold uval in Ha. lia.
  - right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split.
    + apply In_FBx. right. exists t. split; [exact Hin|]. split; [exact Hnz | symmetry; apply surjective_pairing].
    + unfold tvv. cbn [fst snd]. unfold uval in Ha. exact Ha.
Qed.

Lemma V_ldR_500 : V_below 500 V_ldR = true. Proof using . reflexivity. Qed.
Lemma V_ldR_lt : ltac2:(tb__ "0|0|
S12S25S0S18S83R2A1S16A3S4cS25R2S75A3Sb2R3S7S13R4A1A1A2F_;F_;Fv;FA;").
Proof using . intros A v CV Hv. pose proof (proj1 (forallb_forall _ _) V_ldR_500 v Hv) as X. cbv beta in X. apply Pos.ltb_lt in X. apply Pos.leb_le in CV. lia. Qed.

Lemma ldefR_pure : ltac2:(tb__ "0|1|
S12S3S3S0S18S83R3A1S16A3SfS7S13R4A1A1R3R2A3S74R4A1M0G0F_;F_;F_;Frho';Frho;FA;").
Proof using . intros A rho rho' CV (H1 & H2 & H3) HP. exact (ldefR_reads rho rho' (fun v Hv => H1 v (V_ldR_lt A v CV Hv)) H2 H3 HP). Qed.
Lemma ldefR_call : ltac2:(tb__ "0|3|
S12S17S19S2S2A2M0A1S3S3S6bS5S6R2A1S4S13R4A1A1A3S0S18S82S4S13R5A1A1A1S16A3S0S18S83R6A1S16A3S8aS7S13R7A1A1R5R4A3SacVCST;Vrho0;VFB;VFF;R6R7S40R5A8S4cG0S1bS2S2S6fS76A4R8A3S0S24S2dR8S6fA2Z0M1A3S0S24S2dR9S76A2G1A3F_;S74R9A1M2G2F_;F_;F_;F_;F_;F_;F_;F_;Frho';Frho;Fkept;FA;").
Proof using .
  intros A kept rho rho' HF CF CV Hag HK Hin Hnull HP.
  unfold ldef_facts in CF. apply lazy_andb_prop in CF as [F1 CF]. apply lazy_andb_prop in CF as [F2 CF]. apply lazy_andb_prop in CF as [F3 CF].
  apply lazy_andb_prop in CF as [F4 F6].
  pose proof (holds_mem _ _ _ HF F1) as H1. rewrite h_ule, uval_lit in H1 by lia.
  pose proof (holds_mem _ _ _ HF F2) as H2. rewrite h_ule, uval_lit in H2 by lia.
  pose proof (holds_mem _ _ _ HF F3) as H3. rewrite h_ule, uval_lit in H3 by lia.
  pose proof (holds_mem _ _ _ HF F4) as H4. rewrite h_ule in H4.
  pose proof (holds_mem _ _ _ HF F6) as H6. rewrite h_ule, uval_lit in H6 by lia.
  pose proof (uval_range rho xLK) as RK. pose proof (uval_range rho xLD) as RD.
  assert (ESZ : uval rho szL = 16 * uval rho xLK) by (unfold szL, kb; apply uval_mul_lit; lia).
  fold szL in H1, H4. rewrite (uval_add_small rho xLD szL) in H4 by lia.
  apply (ldefR_keep rho rho'); [| | exact HP].
  - intros v Hv. apply (proj1 Hag). pose proof (proj1 (forallb_forall _ _) V_ldR_500 v Hv) as X. cbv beta in X. apply Pos.ltb_lt in X. apply Pos.leb_le in CV. lia.
  - intros z Hz.
    destruct (Z.eq_dec (uval rho xLD) 0) as [E0|Hnz]; [pose proof (Hnull E0); lia|].
    exact (keptK_lines CST FB FF rho0 rho kept frL rho' HK Hin Hnz ltac:(lia) ltac:(unfold B32, Lib_vec_reserve.B32; lia) z Hz).
Qed.

Lemma ldefR_absorb_sh : ltac2:(tb__ "0|4|
S5dS7cS24S3S17S6aQ40A1A1S17S6eA1S6dS22S25S24S25S25S24S24S17S10A1S11S7fS5cVAInv;VCST;VXGL;S80VKc;Vrho0;VP0;VFB;VFF;VBX;S5aR11R10RfReRdRcRbA12S0S1eS19S19S2S24A2M0S2A2M1A1S4fG1S69R12A1RbA3S1cG1S1bG0S2S1bS2S24SaRaA1R9A4SaR8A1A4A2A3S1S42Z0M2RaA2S42RaZ6A2A2S42G2R8A2S1S42R9R8A2S42R8S48Sa6RcA1Z8A2A2A2S6R13SeS15RbA1SaReA1A2A2S6R14SbSaRcA1S8S43S46Z2M3Z3dA2Z1A2A1A2A2S4cS19S2S2A2S1bS2S2S6fS76A4S5eR18A1A3S42S44S2dR16S6fA2S47Z10S2dR16S70A2A2A2S46G3Z2fA2A2S74R17A1S74S77R18S1fS9SafR10RfReRdRcA5S20S9A1A3RbA3A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fvm;Fd;Fcells;Fk2;Fk1;Fg;FpF;Fc;FpR;Fi;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;").
Proof using ALA HCST.
  intros nd Ai kc rho tp tr md i pR c pF g k1 k2 cells d vm HJ Hnth Hc6 Hk1 Hk2 HG1 HG2 Hlin Hk64 HPHI.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & _).
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts segs AInv CST ALA HCST rho0 FF Ai rho tp md (nd_fr nd) fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & _).
  cbn [frv fst snd fe] in E1, F1, F2, F3, F4, F5. set (sz := fs_frame_size c) in *. set (p := uval rho (SVar pR)) in *.
  pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END, SHADOW_OFF, IMG_HI in F4; lia).
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia. change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  set (sh := shobj g k1 k2 cells d).
  assert (Hrng : obj_range rho sh = (Sh p + k1, Sh p + k2)).
  { unfold obj_range, obj_lo_of, obj_hi_of, sh, shobj. cbn [ob_base ob_lo ob_hi eval]. rewrite Ug. unfold Sh, SHADOW_OFF in *. rewrite !soff_lit_small by lia. f_equal; lia. }
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SHAD : forall z, Sh p + k1 <= z < Sh p + k2 -> is_shadowZ z).
  { intros z Hz. pose proof (Sh_is_shadow p ltac:(lia)) as S1. pose proof (Sh_is_shadow (p + sz - 1) ltac:(lia)) as S2. rewrite Sh_last in S2 by lia.
    unfold is_shadowZ in *. lia. }
  assert (Ekb : uval rho szL = 16 * uval rho xLK).
  { unfold szL, kb. pose proof (uval_range rho xLK). pose proof (uval_range rho xLD). apply uval_mul_lit; lia. }
  apply (ldefR_keep rho (rho_absorb rho [sh] vm)); [intros v _; reflexivity | | exact HPHI].
  intros z Hz.
  destruct (Z.eq_dec (uval rho xLD) 0) as [Hz0|Hnz].
  { exfalso. pose proof (proj1 (Forall_forall _ _) HZ _ Hlin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [fst snd] in X.
    specialize (X ltac:(intros Y; apply Y; exact Hz0)). change (bv_unsigned (eval rho szL)) with (uval rho szL) in X. lia. }

  pose proof (proj1 (Forall_forall _ _) HN _ Hlin) as HL. cbv beta in HL.
  assert (Htnz : tnz rho (xLD, szL)) by (unfold tnz; cbn [fst]; exact Hnz).
  destruct (HL Htnz) as (_ & Hlive & _).
  unfold tvv in Hlive. cbn [fst snd] in Hlive. change (bv_unsigned (eval rho xLD)) with (uval rho xLD) in Hlive.
  change (bv_unsigned (eval rho szL)) with (uval rho szL) in Hlive. rewrite Ekb in Hlive.
  apply GlueM.rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr.
  pose proof (uval_range rho xLD) as RD. pose proof (uval_range rho xLK) as RK.
  rewrite u64_lit in Hr by lia. cbn [fst snd] in Hr.
  apply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None z rho tp md HM); [|exact (SHAD z Hr)].
  right; right; left. exists (uval rho xLD), (16 * uval rho xLK). split; [exact Hlive|]. split; [discriminate | lia].
Qed.

Lemma ldef_facts_k : ltac2:(tb__ "0|0|
S3S17S5A1S6bS5S6R2A1R1A3S0S18S82R2A1S16A3S42S2dR4S70A2ZffffffffA2F_;F_;FF;Frho;").
Proof using .
  intros rho F HF CF. unfold ldef_facts in CF. apply lazy_andb_prop in CF as [_ CF]. apply lazy_andb_prop in CF as [F2 _].
  pose proof (holds_mem _ _ _ HF F2) as H2. rewrite h_ule, uval_lit in H2 by lia. exact H2.
Qed.

Lemma ldef_facts_k64 : ltac2:(tb__ "0|0|
S3S17S5A1S6bS5S6R2A1R1A3S0S18S82R2A1S16A3S42S44S2dR4S6fA2S47Z10S2dR4S70A2A2A2S46Z2Z2fA2A2F_;F_;FF;Frho;").
Proof using .
  intros rho F HF CF. unfold ldef_facts in CF.
  apply lazy_andb_prop in CF as [F1 CF]. apply lazy_andb_prop in CF as [F2 CF]. apply lazy_andb_prop in CF as [F3 CF]. apply lazy_andb_prop in CF as [F4 F5].
  pose proof (holds_mem _ _ _ HF F1) as H1. pose proof (holds_mem _ _ _ HF F2) as H2. pose proof (holds_mem _ _ _ HF F3) as H3.
  pose proof (holds_mem _ _ _ HF F4) as H4. pose proof (holds_mem _ _ _ HF F5) as H5.
  rewrite h_ule in H1, H2, H3, H4, H5. rewrite uval_lit in H1, H2, H3, H5 by lia.
  pose proof (uval_range rho xLK) as RK. pose proof (uval_range rho xLD) as RD. pose proof (uval_range rho (SVar 30)) as R30.
  assert (EK : uval rho (kb 16 xLK) = 16 * uval rho xLK) by (unfold kb; apply uval_mul_lit; lia).
  rewrite uval_add_small in H4 by (rewrite ?EK; lia). rewrite EK in H4. lia.
Qed.

Lemma ldefR_keptR : ltac2:(tb__ "0|3|
S12S17S19S2S2A2M0A1S3S3S6bS5S6R2A1S4S13R4A1A1A3S0S18S82S4S13R5A1A1A1S16A3S0S18S83R6A1S16A3S8aS7S13R7A1A1R5R4A3SadR6R7R5A3S4cG0S1bS2S2S6fS76A4R8A3S0S24S2dR8S6fA2Z0M1A3S0S24S2dR9S76A2G1A3F_;S74R9A1M2G2F_;F_;F_;F_;F_;F_;F_;F_;Frho';Frho;Ftv;FA;").
Proof using .
  intros A tv rho rho' HF CF CV Hag HKR Hin Hnull HP.
  pose proof (ldef_facts_k rho _ HF CF) as H2. pose proof (uval_range rho xLK) as RK.
  assert (ESZ : uval rho szL = 16 * uval rho xLK) by (unfold szL, kb; apply uval_mul_lit; lia).
  apply (ldefR_keep rho rho'); [| | exact HP].
  - intros v Hv. apply (proj1 Hag). pose proof (proj1 (forallb_forall _ _) V_ldR_500 v Hv) as X. cbv beta in X. apply Pos.ltb_lt in X. apply Pos.leb_le in CV. lia.
  - intros z Hz.
    destruct (Z.eq_dec (uval rho xLD) 0) as [E0|Hnz]; [pose proof (Hnull E0); lia|].
    apply (HKR (xLD, szL) z Hin); [unfold tnz; cbn [fst]; exact Hnz|].
    unfold tvv. cbn [fst snd]. change (bv_unsigned (eval rho xLD)) with (uval rho xLD). change (bv_unsigned (eval rho szL)) with (uval rho szL). rewrite ESZ. exact Hz.
Qed.

Lemma HIN_vf : ltac2:(tb__ "0|2|
S12S17S9A1S7aS2S24S2S24S3S7fS7cS3S17S6aQ40A1A1S6dS0S18Sa1S4S13RdA1A1S27S40S41RcA5S16A3S0S18Sa3S4S13ReA1A1S27S40Sa2S28ReRbA2A5S16A3S0S2S78RdPcA2ScSa0S81S8R9A1A3A3S0S2S78RePfA2RdA3S0S2S78RfP11A2S87RdRcA2A3S4cS19S2S2A2M0S1bS2S2RfS87ReRdA2A4S27A3S42Z0RdA2S42S44ReZ20A2Z800A2S0S18S4dS5SdSbS81S8Z7fffff7ff800A1A2A1S4S13R15A1A1A3S16A3S6bS5S6RfA1S4S13R16A1A1A3VP0;Vrho0;A1S8aS80Vrho0;R11A3VAInv;R10RfReRdA4S61Vrho0;R11A2S90R14S7eS7dR12A1A1A2S63VFB;R13A2S64VFF;R14A2S5fVFB;R15R17S1aG0S27S1fG0S89S20G0A1A3A3M1A4S92R18G1A2S8fR19G1A2S65VFF;R18R1aS40A4S1S98VCST;Vrho0;VFB;VFF;R1bS27S40R21A8S1S9aVCST;VXGL;Vrho0;VFB;VFF;R1bS27S40S28R22R1fA2A9S9dVCST;S8eVFB;R1bS27A3S94VFF;R1bS40A3S79S77R1bR21R1aA3R20A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;Fo;Fk;Fe;Fd;Fs;FR;FE;").
Proof using ALA HCST HXlits.
  intros E R s d e k o rho ms Ai rho1 tp1 md1 CR CX Hs12 Hs15 Hs17 Hin Ho0 Ho1 CvF HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  assert (HNk : tvinA FB Ai rho kept_ad) by (apply (tvinA_sublist FB Ai rho (kept_ad ++ [blkAR])); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_ad) by (exact (tvd_app_l rho kept_ad [blkAR] HD)).
  assert (HZk : tvz rho kept_ad) by (apply (tvz_sublist rho (kept_ad ++ [blkAR])); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (DP.lo_robjsF0 AInv CST ALA HCST FB FF rho0 Ai rho _ kept_ad R rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_ad (Xk_vf E d) rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold VFP.P0_vf. split.
    + intros a Ha. unfold uval, VF.vV in Ha. cbn [eval] in Ha. rewrite !rw_call', Hs12 in Ha.
      repeat change (bv_unsigned (eval rho ?x)) with (uval rho x) in Ha.
      pose proof (holds_mem _ _ _ HF CvF) as HvF. rewrite h_ule, uval_lit in HvF by lia.
      assert (EA : uval rho (SAlu ALU_ADD vF (SLit o)) = uval rho vF + o).
      { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
      rewrite EA in Ha.
      right; right; right. exists (uval rho vF), 2048, (uval rho vFL). split; [|lia].
      change 2048 with (fs_frame_size 5). apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity].
    + unfold uval, VF.vL, VF.vD. cbn [eval]. rewrite !rw_call', Hs15, Hs17.
      repeat change (bv_unsigned (eval rho ?x)) with (uval rho x).
      destruct (Z.eq_dec (uval rho d) 0) as [Hz|Hnz].
      * left. pose proof (proj1 (Forall_forall _ _) HZk (d, kb e k) Hin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [fst snd] in X.
        exact (X ltac:(intros Y; apply Y; exact Hz)).
      * right; left. exists (uval rho d), (uval rho (kb e k)). split; [|lia].
        apply In_FBx. right. exists (d, kb e k). split; [exact Hin|]. split; [exact Hnz | reflexivity].
Qed.

Lemma lines_in_kept_ad : ltac2:(tb__ "0|0|
S4cS19S2S2A2S1bS2S2S6fS76A4S27A3").
Proof using . vm_compute. repeat (first [left; reflexivity | right]). Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4aS12S3S17S6aQ40A1A1S72S6bS5S6R3A1S4S13R4A1A1A3VTR;S49S3fR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S72S72S72S73R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S72OS72S73R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4aS4aS12S12S7aS17S9A1M0S17S19S12S51A2M1A1S17S19S2S2A2M2A1S72S3S17S6aQ40A1A1M3G2S4cG2R1R5A3S4cG2R2S14RbA1A3F_;Fr;S0S1eG0A1S54RaR9R8A3S1cG0R7A2A3S0S18S53RbRaR9R8S6cG1S12S1dS12S51A2R7A4A5S16A3S3G3VTR;S49S3fRfRdR2R1A5S52S3fS7S13RdA1A1R2R1RaA5A2Ftp1;Frho1;S17S6eA1M4S7fS6dS4bS3fR9R8R10S1bG4S9bR3S9cR2R1A2A4A5R13RaR9R4R2A4R13S79S77RbRfS7bR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S12S51G4S7fS6dS3G3G4S7fS6dS4cG1S1bS12S51RaR9A4R14A3S4bS3fR12R11R19S1bG4S9bR9S9cR8R7A2A4A5R1cR13R12RaR8A4S8aS7S13R1aA1A1S79S77R14R18S7bR9R13RaA3A3R19A2R8A3S4bS3fR9R8ReS1bG4S9bR7S9cR6R5A2A4A5ReS79S77R16R1aS7bRbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sa9R17S7bRcR16RdA3R1bR1cR1dR10R1eR19RbA9S3S8bR18S7bRdR17ReA3R1cR1dS13R1eA1S13R1fA1S13R11A1R1RcA9VTR;S49S3fS55R11S79S77R19R1dS7bReR18RfA3A3R1eA2R18RdRcA5SaaR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S49S3fR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVF : ltac2:(tb__ "0|1|
S17S19S24S24A2M0A1S17S19G0S24A2A1S33S3S17S6aQ40A1A1S30Z4R3A2VTR;S49S3fS60VAInv;VCST;VXGL;VKc;S9dVCST;R6R5A3R6R5R4S5aS37AaS34R3R2A5S52S3fS9eR3R2SabVAInv;VCST;VXGL;VKc;S9dVCST;A1S5aS2aR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Lemma X_BLK : ltac2:(tb__ "0|17|
S12S12S12S12S12S12S12S12S12S12S12S12S12S12S17S9A1M0S2S24S2S24S17S2cA1M1G1G1S2S72S3S17S6aQ40A1A1M2S4cS19S2S2A2M3S1bS2S2RbS87RaR9A2A4S27A3S42Z1c0M4R9A2S42S44RaZ20A2Z6d8A2S0S1eS12A1M5S84R1dS2bR1dS43RbG4A2A2A2S1cS12R1cA2A3S0S18S4dS5SdSbS81S8Z7fffff7ff800A1A2A1S4S13R1dA1A1A3S16A3S0S18S99S28R1eR10A2S14R1eA1A2S16A3S0S1eG0A1S54R1fS34S26R1fA1A3S1cG0R12A2A3S0S18S53R20S34S26R20A1R13S6cS19S19S12S5dA2M6S3S3OF_;F_;M7A2M8S12G8S1dS12S5dS1dG6G7R1A3A3Lp;S2aA4A5S16A3S0S18SaeS80S26R21A1A2S16A3S0S18S8cS26R22A1S9eA2S16A3S0S18Sb1S80S7S13R23A1A1A2S16A3S0S18S68S7S13R24A1A1S56S1aG3S27S1fG3S89S20G3A1A3M9A3MaS40S1aS2cR12R11A3S57S71S16A2MbA4A2S16A3S0S18S31S7S13R25A1A1S1aS2cR13R11A3A2S16A3S0S18S91S26R26A1G9S5eS37A1A3S16A3S0S18S62S59S26R27A1S66S37A1A2GbA2S16A3S0S18Sa4S1aS2cR16R15A3McGcA2S16A3S0S18Sa4S1aS2cR17S1aS2cS2eS26R29A1S67S37A1MdA2MeR15A3A3S1aS2cGeS1aS2cR17R15A3A3A2S16A3S0S18S32R18A1S16A3S0S18S86S4S13R2bA1A1S8Z0MfA1GfR18S1aS2cS2eS26R2bA1GdA2R17A3A5S16A3S0S18S4eS19S95G7A2M10G10S97S34S9eS26R2dA1S7S13R2dA1M11A1S1dS95G7R1A3A5Lp;S2aA3S16A3S0S18Sa1S4G11A1S27S40S41R20A5S16A3S0S18Sa3S4S13R2eA1A1S27S40Sa2S28R2eR20A2A5S16A3S0S2S78S26R2fA1PcA2ScSa0S81S8R1eA1A3A3S0S2S78S26R30A1PfA2R22A3S0S2S78S26R31A1P11A2S87R22R21A2A3S0S18S82S4S13R32A1A1A1S16A3S0S18S83R33A1S16A3S0S12S93S34R34S26R34A1R27S35S28R34R26A2A6R33A3S0G5S84R34S29R34S43R24G4A2A2A2S1cS12R33A2A3S0S12S88R34A1R33A3S0S17G3A1M12S8dS50S26R37A1S34S35R37A4S38A2G9A3S0S58S59S50S26R38A1S34S35R38A4S3cA2GbA3S0S18S85S4S13R36A1A1S1aS2cR27R25A3M13S1aS2cS2eS50S26R39A1S34S35R39A4S3bA2G13A3A3S16A3S0S12S93S34R3aS26R3aA1R2dS39S28R3aR2cA2A6R36A3S0G5S84R37S29R37S43R2aG4A2A2A2S1cS12R36A2A3S0S12S88R37A1R36A3S0G12S8dS50S26R3dA1S34S39R3dA4S38A2G9A3S0S58S59S50S26R3eA1S34S39R3eA4S57S3eS21A2A2S57S71S21A2M14A3S0S12S93S34R3fS26R3fA1R32S3aS28R3fR31A2A6R38A3S0G5S84R39S29R39S43R2fG4A2A2A2S1cS12R38A2A3S0S12S88R39A1R38A3S0G12S8dS50S26R42A1S34S3aR42A4S38A2G9A3S0S58S59S50S26R43A1S34S3aR43A4S57S3dS16A2A2S57R2eS16A2A3S0S12S93S34R44S26R44A1R37S36S28R44R36A2A6R3aA3S0G5S84R3bS29R3bS43R34G4A2A2A2S1cS12R3aA2A3S0S12S88R3bA1R3aA3S0G12S8dS50S26R47A1S34S36R47A4S38A2G9A3S0S58S59S50S26R48A1S34S36R48A4S3cA2GbA3S0S18S85S4S13R3dA1A1S1aS2cR37R35A3M15S1aS2cS2eS50S26R49A1S34S36R49A4S3bA2G15A3A3S16A3S3G2S74R2A1M16VTR;S49S3fVJAv;S56GaS40S1aS2cR3bR39A3GbA4A1R4aR3R2A5R37A2F_;Ftp';Frho';S3G2G16VTR;S49S3fVJAv;S56GaS40S1aS2cR3cR3aA3G14A4A1R48R3R2A5R38A2F_;Ftp';Frho';S3G2G16VTR;S49S3fVJAv;S56GaS40S1aS2cR3dR3bA3S57R3aS16A2A4A1R46R3R2A5R39A2F_;Ftp';Frho';S3G2G16VTR;S49S3fVJAv;S56GaS40S1aS2cR3eR3cA3GbA4A1R44R3R2A5R3aA2F_;Ftp';Frho';S74R37A1VTR;S49S3fVJAv;S56GaS40S1aS2cR3dR3cA3GbA4A1R50R38R37A5R39A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FqHk;Fdupn;Fdupj;Fbcom;Fo;Fk;Fe;Fd;FR;FTy;FTyB;FTy0;FTk;FTkB;FTk0;FTf;FTfB;FTf0;FTz;FTzB;FTz0;FE;FE0;").
Proof using ALA HCST HXGL HXlits HKc HBX TR_facts TR_ex TR_pre TR_pureP TR_callP CVF.
  intros E0 E Tz0 TzB Tz Tf0 TfB Tf Tk0 TkB Tk Ty0 TyB Ty R d e k o bcom dupj dupn qHk Q rho tp
         Hin Ho0 Ho1 HE CvF HXk Hent Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham PP1 PP2 PWc PPay Hpd CR CX Hs12 Hs15 Hs17 CF CV
         HTz0 HTzB HTz Itz Iaz Lz HTf0 HTfB HTf Itf Iaf HTk0 HTkB HTk Itk Iak HTy0 HTyB HTy Ity Iay Ly HZero HFail HOk HZero2 HPHI.
  set (ndj := NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupj) (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndj) E rho tp)).
  { intros w Hw. exact (SPA_axforms segs (JAv ndj) (xf_vf E0 (o - 448)) rho E0 E tp w HE Hw). }
  apply TR_facts. intros HF.

  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndj] in HZ. intros E0'.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [apply in_or_app; left; exact lines_in_kept_ad|].
    unfold tnz. cbn [fst]. intros H. exact (H E0'). }
  intros Hnull.

  unfold ndj.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (VFP.P0_vf CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           VF.Pre_vf VF.nd0 PDk_vf NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVF eq_refl
           E (s_vf E) R (Xk_vf E d) rho tp kept_ad [blkAR] frL (bcom ++ dupj) (bcom ++ dupn) (AHead pH true) Q
           HXk Hent Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - unfold payA. exact (pay_okF_split _ _ _ _ (bcom ++ dupj) _ bcom dupj (bd_subst (s_vf E) (nd_bd VF.nd0) ++ dupn) PP1 PP2 PWc PPay).
  - exact Hpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_vf E R (s_vf E) d e k o rho ms Ai rho1 tp1 md1 CR CX Hs12 Hs15 Hs17 Hin ltac:(lia) ltac:(lia) CvF HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndLd] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : ldefR rho') by exact (ldefR_call E kept_ad rho rho' HF CF CV Hag HK lines_in_kept_ad Hnull HPHI).
    cbn [PDk_vf liftPD VFP.PD_vf map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[Hd|[]]]]]; injection Hd as <- <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VF.nd_zero VF.nd0 VF.nd_fail VF.nd_ok].
    +
      rewrite HTz0, Itz, Iaz.
      apply (TR_pre (SPA segs (JAv (NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupn) (AHead pH true))) Tz rho' tp')); [|exact (HZero rho' tp' HPHI')].
      intros w Hw. apply (SPA_JA_le2 segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (kept_ad ++ [blkAR]) frL _ (bcom ++ dupn) (AHead pH true) Tz rho' tp' w Lz).
      rewrite <- HTz. apply SPA_tidy. exact (SPA_axforms segs _ (xfb_vf Tz0 (o - 448)) rho' Tz0 TzB tp' w HTzB Hw).
    +
      rewrite HTf0, Itf, Iaf. change (bd_subst _ [] ++ ?r) with r.
      apply (TR_pre (SPA segs (JAv (NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupn) (AHead pH false))) Tf rho' tp')); [|exact (HFail rho' tp' HPHI')].
      intros w Hw. rewrite <- HTf. apply SPA_tidy. exact (SPA_axforms segs _ (xfb_vf Tf0 (o - 448)) rho' Tf0 TfB tp' w HTfB Hw).
    +
      rewrite HTk0, Itk, Iak. change (bd_subst _ [] ++ ?r) with r.
      apply (TR_pre (SPA segs (JAv (NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupn) (AHead qHk true))) Tk rho' tp')); [|exact (HOk rho' tp' HPHI')].
      intros w Hw. rewrite <- HTk. apply SPA_tidy. exact (SPA_axforms segs _ (xfb_vf Tk0 (o - 448)) rho' Tk0 TkB tp' w HTkB Hw).
    +
      rewrite HTy0, Ity, Iay.
      apply (TR_pre (SPA segs (JAv (NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupn) (AHead pH true))) Ty rho' tp')); [|exact (HZero2 rho' tp' HPHI')].
      intros w Hw. apply (SPA_JA_le2 segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (kept_ad ++ [blkAR]) frL _ (bcom ++ dupn) (AHead pH true) Ty rho' tp' w Ly).
      rewrite <- HTy. apply SPA_tidy. exact (SPA_axforms segs _ (xfb_vf Ty0 (o - 448)) rho' Ty0 TyB tp' w HTyB Hw).
Qed.
End X.
End Sum.
