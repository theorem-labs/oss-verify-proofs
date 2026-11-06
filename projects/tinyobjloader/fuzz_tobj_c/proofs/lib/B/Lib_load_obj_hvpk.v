(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "holds"; "sobj"; "SVar"; "ss_facts"; "SLit"; "SPEq"; "SPUle"; "cell"; "odefault"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "pair"; "cons"; "nil"; "fst"; "snd"; "Some"; "nat"; "None"; "andb"; "option"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tblB"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "True"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "div"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "xLK"; "xLC"; "pI"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "TPA"; "frinA"; "tvinA"; "JAi"; "NDA"; "PTrue"; "amode"; "nd_fr"; "nd_tv"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "xextraLO"; "robjs_chkC"; "xrs_chkC"; "xr_inlits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "extra_hv"; "PhisH"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "g8"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "wclear"; "xlocal"; "shobj"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk.Sum"; "extraXlo"; "f5_locals"; "xr_f5local"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xr_eqb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import LOAddr LOLAddr.

Lemma PhisH_reads : ltac2:(tb__ "0|3|
S39SfSeS1A1M0S3OF_;M1A2M2G2S71S15G0G1R1A3S16G0G1R1A3A2Lp;S56A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S2eS3SeS38Q40A1A1S31OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S74S63VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S20S25Z0R2A2S26R2S61A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S4fVXGL;R1A2S20S25Z0R2A2S26R2S61A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S0S64R1A1S4fVXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
SeSfSfS0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
S69VCST;VFB;VFF;A3").

Lemma lo_robjsF : ltac2:(tb__ "0|1|
S2eS3SeS4A1SeSfS2S2A2M0A1SeS6A1S3SeS38Q40A1A1S31VAInv;R8R3R2R1A4S39S4S5R8A1R7A3VP0;Vrho0;A1S3fS33Vrho0;RaA3S45Vrho0;RcA2S40RcS30S2fRdA1A1A2S47VFB;ReRdRbA4S41ReRcA2S42RfRdA2S46VFF;R11R10S1dA4S1fS10S50R10A1S11A3S3aG0S12S2S2S34S3eZ10S35A2A4R10A3S1fS10S52R12R11S1dS55R10A5S11A3S6eVCST;Vrho0;VFB;VFF;R14R12S1dR11A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CLN Hlin CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extra_hv R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. unfold extra_hv in HE. apply lazy_orb_prop in HE as [HE|HE].
  - exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
  - exact (robj_ent_pclMA CST rho0 FB FF rho _ _ tv frL o a HF CLN HT0 HZ Hlin HE Hr).
Qed.
Lemma lo_xrsF : ltac2:(tb__ "0|1|
S2eS3SeS4A1SeSfS2S2A2A1M0G0S3SeS38Q40A1A1S31VAInv;R8R3R2R1A4S39S4S5R8A1R7A3VP0;Vrho0;A1S3fS33Vrho0;RaA3S45Vrho0;RcA2S40RcS30S2fRdA1A1A2S47VFB;ReRdRbA4S41ReRcA2S42RfRdA2S46VFF;R11R10S1dA4S1fS10S53R10RfS1dS51ReA5S11A3S70VCST;VXGL;Vrho0;VFB;VFF;R12R10S1dRfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tv frL xextraLO X rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
  intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho tv frL r a Hav HP0 HE Ha).
Qed.
Lemma lo_robjsR : ltac2:(tb__ "0|1|
S2eS3SeS4A1SeSfS2S2A2M0A1SeS6A1S3SeS38Q40A1A1S31VAInv;R8R3R2R1A4S39S4S5R8A1R7A3VP0;Vrho0;A1S3fS33Vrho0;RaA3S45Vrho0;RcA2S40RcS30S2fRdA1A1A2S47VFB;ReRdRbA4S41ReRcA2S42RfRdA2S46VFF;R11R10S1dA4S1fS10S50R10A1S11A3S3aG0S12S2S2S34S3eZ10S35A2A4R10A3S1fS10S57R12R11S1dS55R10A5S11A3S73VCST;Vrho0;VFB;VFF;R14R12S1dR11A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CLN Hlin CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkR_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extra_hv R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. unfold extra_hv in HE. apply lazy_orb_prop in HE as [HE|HE].
  - exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
  - exact (robj_ent_pclMA CST rho0 FB FF rho _ _ tv frL o a HF CLN HT0 HZ Hlin HE Hr).
Qed.

Lemma site_rt_lo : ltac2:(tb__ "0|1|
S5aS6bSeS6A1S3SeSfS2S2A2M0A1SeS2dA1S4bS1fS10S52S8S58R7A1A1R3S1dS55R5A5S11A3S1fS10S53S8S58R8A1A1R4S1dS51S59R8A1A5S11A3S1fS10S50S8S58R9A1A1A1S11A3S3aG0S12S2S2S34S3eZ10S35A2A4R6A3S72VAInv;VCST;VXGL;S33Vrho0;VP0;VFB;VFF;RbRaR9R8S49R7S1dR6R5A4S19S0A1S2eS5cS23L_;L_;AfF_;F_;F_;F_;Fam;Fbd;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv bd am CR CX CLN Hlin Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (lo_robjsF Ai rho _ tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CLN Hlin CR) as HRF.
  pose proof (lo_xrsF Ai rho _ tv (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX) as HXF.
  assert (HN' : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.fbinA_FBx FB Ai rho tv [] HBf HN') as FBX. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.ffinA_FFx FF Ai rho frL HFF HFR) as FFX.
  split; [|split; [|exact I]].
  - intros o a Ho Hr. eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact (HRF o a Ho Hr)].
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact Hc].
Qed.

Definition f5_locals : list (Z * Z) := ltac2:(tb__ "0|1|
S13SfS0S0A2M0S12S0S0Z170Z30A4S13G0S12S0S0Z1c0Z518A4S14G0A1A3A3").
Definition xr_f5local (k1 k2 : Z) (r : sv * sv) : bool := ltac2:(tb__ "0|1|
S3bSfS0S0A2M0G0S1aS6fVr;S5eP6eR1A2A2S5dVk1;Vk2;S15S0S0R1A3S16S0S0R1A3A4A2Lol;S66A3").
Definition extraXlo (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S10S10L_;S51Vr;A1S11S54Vr;A1X10x2").
Definition xrs_chkRo (facts : list sprop) (tv : list (sv * sv)) (k1 k2 : Z) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S3cSfS2S2A2M0G0S1cS67Vk1;Vk2;R1A3S60VXGL;Vfacts;Vtv;S1dS17S18U0A2S14S6A1S65S13G0R1S14G0A1A3A8A2Lr;VX;A3").

Lemma lo_xrsRo : ltac2:(tb__ "0|3|
S2eS3SeS4A1SeSfS2S2A2M0A1M1G1S3SeS38Q40A1A1S31S0S0VAInv;RaR5R4R3A4S39S4S5RaA1R9A3VP0;Vrho0;A1S3fS33Vrho0;RcA3S45Vrho0;ReA2S40ReS30S2fRfA1A1A2S47VFB;R10RfRdA4S41R10ReA2S42R11RfA2S46VFF;R13R12S1dA4S1fS10S68R12R11RcRbR10A5S11A3G0S0S3aG0R2R13A3S20S25S2cR17S15S2S2R3A3A2M2R2A2S26R2S27G2S2cR17S16S2S2R3A3A2A2A2A2S22S22S6dVCST;Vrho0;S43VFB;R18R16A3S6cVFF;R18S44SfSfS2S0A2S2A2U0S1dA3A3R3A5S4fVXGL;R3A2A2S21S0S0S21S0S0S20S1fG0R6S5eP6eS12S0S0R2R1A4A2A3S20S25Z0R2A2S20S25Z1R1A2S20S25S27R2R1A2S62Z5A1A2S1fS10S5dR13R12R2R1A4S11A3A2A2A2A2Llen;A2Loff;A2A2F_;F_;Fy;Fr;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fk2;Fk1;Fmd1;Ftp1;Frho1;FX;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv X rho1 tp1 md1 k1 k2 HM HF HP0 Hav HT HTK HN HD HZ HFR Hchk r y Hr Hy.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  unfold xrs_chkRo in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. cbv beta in Hc. apply orb_prop in Hc as [Hc|Hc].
  - right. unfold xr_f5local in Hc. apply existsb_exists in Hc as ([off len] & Hin & Hc). apply andb_prop in Hc as [He Hw]. apply xr_eqb_sound in He.
    exists off, len. split; [exact He|]. cbn [fst snd] in Hw. change (fs_frame_size 5) with 2048.
    cbn [f5_locals In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; (split; [lia | split; [lia | split; [lia | exact Hw]]]).
  - left.
    apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv frL (Some 0%nat) [] extraXlo [r] rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hc) with (r := r);
      [| left; reflexivity | exact Hy].
    intros r' a' [<-|[]] HE Ha. unfold extraXlo in HE. apply lazy_orb_prop in HE as [HE|HE].
    + left. exact (xextraLO_pclMA CST rho0 FB FF rho tv _ r a' Hav HP0 HE Ha).
    + right. apply HXlits. exact (xr_inlits_sound r rho a' HE Ha).
Qed.

Lemma tblB_absorb_sh : ltac2:(tb__ "0|5|
S4eS2eS0S3SeS38Q40A1A1SeS32A1S31S18S1S0S1S1S0S0SeScA1SdS5cS48VAInv;VCST;VXGL;S33VKc;Vrho0;VP0;VFB;VFF;VBX;S4aR11R10RfReRdRcRbA12S1fS1bSfSfS2S0A2M0S2A2M1A1S3dG1S4cR12A1RbA3S17G1S12G0S2S12S2S0S7RaA1R9A4S7R8A1A4A2A3S20S25Z0M2RaA2S25RaZ6A2A2S25G2R8A2S20S25R9R8A2S25R8S29S62RcA1Z8A2A2A2S5R13SaS5bRbA1S7ReA1A2A2S5R14SbS7RcA1S9S2bS28Z2M3Z3dA2Z1A2A1A2A2S3aSfS2S2A2S12S2S2S34S3eZ10M4S35A2A4S4dR18A1A3S24S1fS0S2cR16S34A2G2A3A1S25S27S2cR17S34A2S2aG4S2cR17S35A2A2A2S28G3Z2fA2A2S26S2cR18S37A2S2cR18S36A2A2S25S2cR19S36A2S2cR19S35A2A2S1eR1aA1S1eS6aR1bS13S6S5fR13R12R11R10RfA5S14S6A1A3ReA3A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fvm;Fd;Fcells;Fk2;Fk1;Fg;FpF;Fc;FpR;Fi;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;").
Proof using ALA HCST.
  intros nd Ai kc rho tp tr md i pR c pF g k1 k2 cells d vm HJ Hnth Hc6 Hk1 Hk2 HG1 HG2 Hlin Hnz Hk64 HiC Hck HPHI.
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

  pose proof (proj1 (Forall_forall _ _) HN _ Hlin) as HL. cbv beta in HL.
  assert (Htnz : tnz rho (xLD, kb 16 xLK)) by (unfold tnz; cbn [fst]; exact Hnz).
  destruct (HL Htnz) as (_ & Hlive & _).
  assert (Ekb : uval rho (kb 16 xLK) = 16 * uval rho xLK).
  { unfold kb. pose proof (uval_range rho xLK). pose proof (uval_range rho xLD). apply uval_mul_lit; lia. }
  unfold tvv in Hlive. cbn [fst snd] in Hlive. change (bv_unsigned (eval rho xLD)) with (uval rho xLD) in Hlive.
  change (bv_unsigned (eval rho (kb 16 xLK))) with (uval rho (kb 16 xLK)) in Hlive. rewrite Ekb in Hlive.
  apply (tblB_kept rho (rho_absorb rho [sh] vm)); [intros v _; reflexivity | | exact HiC | exact Hck | exact HPHI].
  intros z Hz. apply GlueM.rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr.
  pose proof (uval_range rho xLD) as RD. pose proof (uval_range rho xLK) as RK.
  rewrite u64_lit in Hr by lia. cbn [fst snd] in Hr.
  apply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None z rho tp md HM); [|exact (SHAD z Hr)].
  right; right; left. exists (uval rho xLD), (16 * uval rho xLK). split; [exact Hlive|]. split; [discriminate | lia].
Qed.
End Sum.
