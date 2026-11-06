(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "bool"; "cons"; "nil"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rw"; "ss_facts"; "sobj"; "sprop"; "DUnknown"; "SLit"; "SPEq"; "SPUle"; "SVar"; "holds"; "ob_cells"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "NDA"; "AHead"; "JA_pre"; "JA"; "nd_below"; "ok_frameKA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "V_B"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf"; "P0_vr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "ndXE"; "VLA"; "z0"; "RL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "g5"; "NP"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "nd_keep"; "PDk_vr"; "h0"; "tv_keep"; "T_failr"; "objs_nl"; "sh_of"; "tv_fail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3m"; "E_o1"; "X_cpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "X_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3.VR"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3e"; "cutsH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "PhisH"; "mH"; "extra_hv"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bitem"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3f"; "lx_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf1"; "loopF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf4.Sum.X"; "rel_chkG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_build_line_index_rom_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hvpk Lib_load_obj_hv2 Lib_load_obj_hv_pf1 Lib_load_obj_hv3 Lib_load_obj_hv3m Lib_load_obj_hv3e Lib_load_obj_loopE Lib_load_obj_hv3f Lib_load_obj_hv_pf3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Ltac inl := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma lines_in_tv_keep : ltac2:(tb__ "0|0|
S35S0S11S11A2S1S11S11S55S40Z10S56A2A4S4cA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma VB_meas4 : ltac2:(tb__ "0|0|
SaS29S5S3aR1S2fA2S4A3S2aS71P1ccR2A2S71P1d3R2A2A2F_;Fn;").
Proof.
  intros n H. split; [apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto | apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto].
Qed.
Lemma VB_460 : In 460%positive V_B /\ In 467%positive V_B. Proof. split; cbn; tauto. Qed.

Lemma efmeasA_VLA_agree : ltac2:(tb__ "0|7|
ScScS20S20S3S3S9S9S12S12S29S28Q40A1M0S13R1P1ccM1A2S13R2G1A2A3S29G0S13R2P1d3M2A2S13R3G2A2A3S29S9S37S1S0S0ScS20A2M3S3A2M4S0S9S11A2M5S1G3S3S1ScS20RcRaA4R8A4S1S9S11R6S43R5S44A2A4M6A4R3A2S37S1G4G5S1G3S3S1ScS20RbR9A4R7A4G6A4R4A2A3F_;F_;Frho';Frho;Fph;Fr;Fk';Fk;Fnd';Fnd;FX';FX;").
Proof.
  intros X X' nd nd' k k' r ph rho rho' H460 H467. unfold efmeasA. cbn [ef_rank ef_var fst snd]. f_equal. f_equal.
  unfold VLA, z0, xLC, pI. cbn [eval]. rewrite H460, H467. reflexivity.
Qed.
Lemma hv3_facts_loop : ltac2:(tb__ "0|0|
S77S14SdS52A1A1A1").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S7dS12S2S28Q40A1A1S73OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S70SbVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S9S58VCST;R1A2S2aS3cZ0R2A2S3dR2S6bA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S9S58VXGL;R1A2S2aS3cZ0R2A2S3dR2S6bA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S9S74R1A1S58VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S0S0S9S9A2S9A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S12OFr;") := ltac2:(tb__ "0|0|
S79VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S25VAInv;VCST;VXGL;S47VKc;Vrho0;VP0;VFB;VFF;VBX;S21Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S39VAInv;VCST;VXGL;S47VKc;Vrho0;VP0;VFB;VFF;VBX;S21VPhi;Vnd;Ad").

Lemma CXR_mk : ltac2:(tb__ "0|0|
S29S5S61VXGL;S14SdS52A1A1S4cZ4Z12S59A6S4A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_fail : ltac2:(tb__ "0|0|
S29S5S61VXGL;S14SdS4dA1A1S50Z4Z12S59A6S4A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2cScS12S2S28Q40A1A1S31S72S16S1cR3A1S14SdR4A1A1A3VTR;S2bSbR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S31S31S31S34R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S31OS31S34R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").

Definition rel_chkG (tv : list (sv * sv)) (bd : list bitem) (L : list (Z * Z)) (E0 Er : axst) : Prop := ltac2:(tb__ "0|6|
S2aS29S2S15A1S1fSdVE0;A1M0A1S8S15S4eVE0;A1M1S6S15S7cS46Z4M2Z12M3S1dS4fVE0;A1A1M4S17A5S7S15A1A3A3A3S2aS29S11SeVE0;A1S18S6cA1A3S2aS29S5S10S6S16S19SfS46A1S48A2S6S16S1aS1bS46A1S18S3fS3eZ2Z3dA2Z1A2A1A2S7S16A1A3A3S14G0A1M5A2S4A3S2aS29S5S36S0S9S9A2S7aG4S17G2G3A4VL;A3S4A3S2aS29S5S26S1eG0A1S22Vtv;S2eVbd;S23S54S4A2A4A2S4A3S2aS29S5S60G5Vtv;S2eS5fG1A5S4A3S2aS29S5S75G5A1S4A3S29ScS7bVE0;G1P6eVL;A4VEr;A3A2A2A2A2A2A2A2").
Lemma site_relG : ltac2:(tb__ "0|3|
S2S0S11S11A2M0A1S2S67A1S2S0S9S9A2A1ScScS12S2S28Q40A1M1A1S31S78R8R7R6R5R4A5S35G0S1S11S11S55S40Z10S56A2A4R9A3S2dR5A1S12S2dR1A1SaS35SaR1S2fA3S29G1S13R4R2A2S13RaR2A2A3F_;Fv;VTR;S2bSbVJAv;S22ReS2eRdS23S54S4A2M2A4A1RaR3R8A5R7A2F_;F_;Frho1;VTR;S2bSbVJAv;S22RcS2eRbG2A4A1R9R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;FEr;FE0;FL;Fbd;Ftv;").
Proof using ALA HCST HXGL LFSH HKc HBX TR_facts TR_pre TR_exw TR_pureP.
  intros tv bd L E0 Er rho tp Q (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8) Hlin HPHI HK.
  set (nd := NDA tv frL bd (AHead pH true)).
  apply TR_facts. intros HF0.
  apply (TR_pre (fun w => exists rho1, (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v) /\ SPA segs (JAv nd) Er rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 4 18 (ob_cells (sh_of E0)) DUnknown] (vms md tp ms)). split.
    - split; [|intros v _; reflexivity].
      destruct Hw as [Hsm (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & HM & HT & _ & _ & (_ & _ & HZ) & _). cbn [nd_tv nd] in HZ.
      pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
      destruct (lines_blk rho _ (topG (aa_geom Ai)) HF0 R7 HTK) as (_ & HiC & HcK & _ & _ & Htop).
      pose proof (lines_nz rho _ (topG (aa_geom Ai)) tv HF0 R7 HTK HZ Hlin) as Hnz.
      pose proof (has_facts_sound rho _ _ HF0 R3) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
      pose proof (topG_range (aa_geom Ai)) as TG.
      apply (tblB_absorb_sh AInv CST XGL ALA HCST Kc FB FF BX rho0 nd Ai kc rho tp tr md 0%nat 110%positive 5 120%positive g5 4 18 _ DUnknown _ HJ frL_0);
        [lia | lia | change (fs_frame_size 5) with 2048; lia | exact HG1 | exact HG2 | exact Hlin | exact Hnz | lia | exact HiC | exact HcK | exact HPHI].
    - rewrite <- R8.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tv frL bd (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 18 (ob_cells (sh_of E0)) DUnknown E0 (objs_nl E0) L rho tp tr ms md
               frL_0 ltac:(lia) R2 R1 ltac:(lia) ltac:(change (fs_frame_size 5) with 2048; lia) eq_refl R3 R4 R5); [|exact Hw].
      intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
      exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tv (objs_nl E0) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR R7 Hlin R6). }
  apply TR_exw. intros rho1.
  apply (TR_pureP _ (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v)); [intros w [H _]; exact H|]. intros [HPHI1 HV1].
  apply (TR_pre (SPA segs (JAv nd) Er rho1 tp)); [intros w [_ Hw]; exact Hw|]. exact (HK rho1 HPHI1 HV1).
Qed.

Lemma latch_rel : ltac2:(tb__ "0|5|
S2S0S11S11A2M0A1M1S2S67A1M2G1G2ScScScScS63S12S2S28Q40A1M3A1S31S76RcRbRaR9R8R7R6R5R4A9S35G0S1S11S11S55S40Z10S56A2A4RdA3S2dR5A1S12SaS35SaR1S2fA3S29G3S13R3R2A2S13R9R2A2A3F_;Fv;S2dS62R2R9A2A1VTR;S2bSbVJAv;S22S30S2eRfS23S54S4A2M4A4A1ReS62R3RaA2R8A5R7A2F_;F_;Frho1;VTR;S2bSbVJAv;S22R10S2eRfG4A4A1RbR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fs;FLb;FLr;FL;FX;Fbdj;Ftvj;Fbd;Ftv;").
Proof using ALA HCST HXGL LFSH HKc HBX TR_facts TR_pre TR_exw TR_pureP.
  intros tv bd tvj bdj X L Lr Lb s rho tp Q
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & Cent & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & CV & _ & _ & Cperm & _) Hlin HPHI HK.
  assert (CREL : rel_chkG tv bd [] L Lr) by (exact (conj C1 (conj C2 (conj C3 (conj eq_refl (conj C4 (conj C5 (conj C6 C7)))))))).
  apply (site_relG tv bd [] L Lr rho tp Q CREL Hlin HPHI). intros rho1 HPHI1 HV1.
  apply (TR_pre (SPA segs (JAv (NDA tvL frL bdj (AHead pH true))) X (rho_sub rho1 s) tp));
    [|exact (HK rho1 HV1 (phi_sub V_B tblB tblB_reads s rho1 CV HPHI1))].
  intros w Hw.
  pose proof (SPA_axforms segs (JAv (NDA tv frL bd (AHead pH true))) (xf_tail Lr) rho1 Lr Lb tp w C8 Hw) as Hw1.
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lb X s (NDA tv frL bd (AHead pH true)) tvj bdj (AHead pH true) tblB V_B rho1 tp w
              tblB_reads Cent Cid Cnp Cnb Ctv Cfr Cbd Cam CV HPHI1 Hw1) as [_ Hw2].
  exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvj tvL frL bdj (AHead pH true) X (rho_sub rho1 s) tp w Cperm Hw2).
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S27SbVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S6eSbS6dVAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XKO1 : ltac2:(tb__ "0|1|
S12S2S28Q40A1A1M0G0S33SbVok;S2bSbVJAFv;S2dS49A2S51R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S12S2S28Q40A1A1M0G0S33SbVok;S2bSbVJAFv;S2dS42A2S57R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHVR_T : ltac2:(tb__ "0|1|
S2S0S9S9A2M0A1S2S0G0S9A2A1S68S12S2S28Q40A1A1S66Z3R3A2S33SbVok;S2bSbS24VAInv;VCST;VXGL;VKc;S3bR6R5A2R6R5R4S21S69S4bS4S5bA3AaS5aR3R2A5S64SbS65R3R2S6aVAInv;VCST;VXGL;VKc;S3bS21S4aR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k segs AInv CST XGL Kc P0_vr PTrue VR.Pre_vr (ndh h0 true VR.nd0) (PDh PD_vr h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc P0_vr PTrue VR.Pre_vr VR.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (vec_reserve_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUT3_T : ltac2:(tb__ "0|4|
ScS20S3S0S9S11A2M0S12S2S28Q40A1A1M1G1S35S0S0S0ScS20A2M2S3A2M3G0A2S1G3G0S1G2S3S1ScS20R7R6A4R5A4R4A4S5cA3S38S5dR6R4A3S33SbVok;S2bSbVJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKO1 XLATCHE2.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_m NP (map efdrop cutsH3) (map efdrop exitsH3) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisH _ _ _ _ _ ecertH3_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsH3 In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (site_mc AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_pre segs ok) tv_keep bd_keep X_hv X_cpk T_mck rho1 tp1 _
             hv3_checks_mk lines_in_tv_keep CXR_mk HP1).
    intros rho' tp' HP' _.
    exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH3) T_mck nd_keep 1%nat (FAMQ tp0') rho' tp'
             ltac:(cbn [map efdrop cutsH3 fst]; inl) HP').
  -
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKO1 rho1 tp1 tp0')].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (latch_rel (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok)
             tv_fail brest_vr tv_vr [LAX 0; LAXK 0] X_latchE2 X_rlF X_rlFr X_rlFb s_rlF rho1 tp1 _ hv3_checks_rlF lines_in_tv_fail HP1).
    intros rho2 _ HP2.
    apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s_rlF) tp1 _ HP2).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 (rho_sub rho2 s_rlF) tp1 tp0')].
Qed.

Theorem kvr_T : ltac2:(tb__ "0|1|
S12S2S28Q40A1A1M0G0S33SbVok;S2bSbVJAFv;S2dS41A2S53R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKO1 XLATCHE2.
  intros rho tp tp0.
  apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  apply (site_vr AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
           (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CHVR_T rho tp _ CXR_fail HPHI).
  - intros rho' tp' HP' _. exact (CUT3_T T_keepS nd_keep 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH3]; inl) HP').
  - intros rho' tp' HP' _. exact (CUT3_T T_grownS nd_grown 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH3]; inl) HP').
  - intros rho' tp' HP' _. exact (CUT3_T T_fail nd_fail 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH3]; inl) HP').
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6fSbS6dVAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
S9S2S28Q40A1A1S31F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S9S9S2S28Q40A1A1S34S3cR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XKO1 : ltac2:(tb__ "0|2|
S12S2S28Q40A1A1M0G0S32SbS2bSbVJAFv;S2dS49A2S51R3R2A5VFAM;S37S1S0S0ScS20A2M1S3A2S0S9S11A2S1G1S3S1ScS20S51S49A4U1A4S5eZfZ3cA2A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S12S2S28Q40A1A1M0G0S32SbS2bSbVJAFv;S2dS42A2S57R3R2A5VFAM;S37S1S0S0ScS20A2M1S3A2S0S9S11A2S1G1S3S1ScS20S57S42A4U1A4S1S9S11S45S43Z1S44A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHVR_E : ltac2:(tb__ "0|1|
S2S0S9S9A2M0A1S2S0G0S9A2A1S68S12S2S28Q40A1A1S66Z3R3A2S32SbS2bSbS24VAInv;VCST;VXGL;VKc;S3bR6R5A2R6R5R4S21S69S4bS4S5bA3AaS5aR3R2A5S64SbS65R3R2S6aVAInv;VCST;VXGL;VKc;S3bS21S4aR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc P0_vr PTrue VR.Pre_vr (ndh h0 true VR.nd0) (PDh PD_vr h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc P0_vr PTrue VR.Pre_vr VR.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (vec_reserve_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUT3_E : ltac2:(tb__ "0|5|
ScS20S3S0S9S11A2M0S12S2S28Q40A1A1M1S9G1S35S0S0S0ScS20A2M2S3A2M3G0A2S1G3G0S1G2S3S1ScS20R8R7A4R6A4R5A4S5cA3S38S5dR7R5A3S2aS3cZ0S37S1G3G0S1G2S3S1ScS20RaR9A4R8A4R7A4R6A2M4A2S3dG4R4A2A2S32SbS2bSbVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKO1 XLATCHE2.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_m NP cutsH3 exitsH3 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH3_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  cbn [exitsH3 In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho1 _ HF0 hv3_facts_loop) as [HiC Hc26].
    apply (site_mc AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_pre segs) tv_keep bd_keep X_hv X_cpk T_mck rho1 tp1 _
             hv3_checks_mk lines_in_tv_keep CXR_mk HP1).
    intros rho' tp' HP' HVB. destruct VB_460 as [I460 I467].
    apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH3 T_mck nd_keep 1%nat (mH 15 70) _ _ rho' tp' ltac:(cbn [cutsH3]; inl) HP').
    apply (VLA_lt2 rho1 rho' 15 15 80 70 X_cpk T_mck nd_keep nd_keep 1%nat 1%nat); [exact (HVB _ I460) | exact (HVB _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia].
  -
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKO1 rho1 tp1 tp0')].
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    pose proof hv3_checks_rlF as CK. pose proof CK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
    destruct VB_460 as [I460 I467].
    apply (latch_rel (etriple segs) (TRe_facts segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs)
             tv_fail brest_vr tv_vr [LAX 0; LAXK 0] X_latchE2 X_rlF X_rlFr X_rlFb s_rlF rho1 tp1 _ CK lines_in_tv_fail HP1).
    intros rho2 HV2 HP2.
    apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s_rlF) tp1 _ HP2).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    rewrite <- (efmeasA_VLA_agree X_latchE2 X_rlF ndXE nd_fail 1%nat 1%nat RL 1 rho1 rho2 (HV2 _ I460) (HV2 _ I467)).
    rewrite <- (efmeasA_VLA_sub X_latchE2 X_latchE2 ndXE ndXE 1%nat 1%nat RL 1 s_rlF rho2 W460 W467).
    exact (XLATCHE2 (rho_sub rho2 s_rlF) tp1 tp0').
Qed.

Theorem kvr_E : ltac2:(tb__ "0|2|
S12S2S28Q40A1A1M0G0S32SbS2bSbVJAFv;S2dS41A2S53R3R2A5VFAM;S37S1S0S0ScS20A2M1S3A2S0S9S11A2S1G1S3S1ScS20S53S41A4U1A4S5eZfZ64A2A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKO1 XLATCHE2.
  intros rho tp tp0.
  apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv3_checks_rel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
  apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
  destruct VB_460 as [I460 I467].
  assert (MM : forall rho' (T : axst) nd, (forall v, In v V_B -> rw rho' v = rw rho v) ->
            0 <= efmeasA (T, nd, 1%nat, mH 15 99) rho' < efmeasA (K_vr, ndA1, 1%nat, mH 15 100) rho).
  { intros rho' T nd HV. apply (VLA_lt2 rho rho' 15 15 100 99 K_vr T ndA1 nd 1%nat 1%nat); [exact (HV _ I460) | exact (HV _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  apply (site_vr AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
           (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CHVR_E rho tp _ CXR_fail HPHI).
  - intros rho' tp' HP' HV. exact (CUT3_E T_keepS nd_keep 1%nat (mH 15 99) rho' tp' _ tp0 ltac:(cbn [cutsH3]; inl) HP' (MM rho' T_keepS nd_keep HV)).
  - intros rho' tp' HP' HV. exact (CUT3_E T_grownS nd_grown 1%nat (mH 15 99) rho' tp' _ tp0 ltac:(cbn [cutsH3]; inl) HP' (MM rho' T_grownS nd_grown HV)).
  - intros rho' tp' HP' HV. exact (CUT3_E T_fail nd_fail 1%nat (mH 15 99) rho' tp' _ tp0 ltac:(cbn [cutsH3]; inl) HP' (MM rho' T_fail nd_fail HV)).
Qed.
End Existence.
End Sum.
