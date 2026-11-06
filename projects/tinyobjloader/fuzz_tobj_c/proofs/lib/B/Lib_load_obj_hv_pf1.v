(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "sv"; "ss_facts"; "holds"; "agree_below"; "sobj"; "SPUle"; "sprop_eqb"; "SLit"; "SVar"; "rw"; "sprop_below"; "SPUlt"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "pair"; "prod"; "Some"; "option"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "jpostA"; "call_checkA"; "J_ofPA"; "LQPA"; "call_checkPA"; "import_postA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "E_hv0"; "K_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "Posts_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "tvL"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Pre_sd"; "Posts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bd_wpos"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "K_hv0c"; "R_sd"; "cur0"; "cur_of"; "s_sd"; "sd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv1c"; "cur_ok"; "sd_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv2"; "R_da"; "da_chk"; "da_ok"; "s_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf1.Sum"; "loopF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA"; "PTrue";
"nd_below"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_build_line_index_rom_call.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hvpk Lib_load_obj_hv2 Lib_load_obj_hv1c Lib_load_obj_hv1e.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Lemma lines_in_tvL : ltac2:(tb__ "0|0|
S2aS1aSaSaA2S19SaSaS44S57Z10S45A2A4S4dA3").
Proof. cbn. do 18 right. left. reflexivity. Qed.
Lemma frL_0 : ltac2:(tb__ "0|2|
S5S1cS1aS1aSaS24A2M0SaA2M1A1S2dG1S4eU0A3S1bG1S19G0SaS19SaS24S12P6eA1Z5A4S12P78A1A4A2A3"). Proof. reflexivity. Qed.

Lemma da_ok_ent : ltac2:(tb__ "0|3|
S0S5S17S63R1A1S18A3S6S5S1cS16SeA1M0A1S33R2S4aS64R2A1M1A3S1bG0S61R2A1M2A2A3S5S17S35R2S4aG1G2S28S2S0S3S4bA4A5S18A3A2F_;FE;").
Proof. intros E H. unfold da_ok, R_da in *. destruct (entails_frA E Pre_da (s_da E)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.

Lemma sd_ok_ent : ltac2:(tb__ "0|3|
S0S5S17S5eR1A1S18A3S6S5S1cS16SeA1M0A1S33R2S4fS5dR2A1M1A3S1bG0S5aR2A1M2A2A3S5S17S35R2S4fG1G2S28S2S0S3S50A4A5S18A3A2F_;FE;").
Proof. intros E H. unfold sd_ok, R_sd in *. destruct (entails_frA E Pre_sd (s_sd E)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.

Lemma cur_ok_holds : ltac2:(tb__ "0|0|
S0S0S7S5S17S5fR3R2A2S18A3S27S8ScR2A1SbS1R3A1A1A3ScR3SfS5bS5cR4A1A2A2F_;F_;Frho;FT0;FE;").
Proof.
  intros E T0 rho H HF. unfold cur_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem rho _ _ HF H2) as F2. rewrite h_ule in F2. rewrite h_ule.
  apply orb_prop in H1 as [H1|H1].
  - apply sv_eqb_sound in H1. rewrite H1. exact F2.
  - pose proof (holds_mem rho _ _ HF H1) as F1. rewrite h_ule in F1. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S72S7S16S26Q40A1A1S2eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S71S1eVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S24S46VCST;R1A2S6S47Z0R2A2S48R2S56A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S24S46VXGL;R1A2S6S47Z0R2A2S48R2S56A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S24S58R1A1S46VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S16S1aS1aS24S24A2S24A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S7OFr;") := ltac2:(tb__ "0|0|
S67VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S6bVAInv;VCST;VXGL;S3eVKc;Vrho0;VP0;VFB;VFF;VBX;S6cVnd;Ac").

Lemma payA_same : ltac2:(tb__ "0|1|
S16S8A1S16S55A1S5S17S54R1A1S18A3S70S3eVrho0;VP0;R3S11Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Definition loopF (F : list sprop) : Prop := ltac2:(tb__ "0|0|
S6S5S17S2bS8S10S15S43S42A2A1VF;A3S18A3S6S5S17S2bS8S10SfS42S3fA2A1VF;A3S18A3S5S17S2bS8S10SfS3fS11Z4000000A1A2A1VF;A3S18A3A2A2").
Lemma loopF_vals : ltac2:(tb__ "0|1|
S7S16S8A1S27S8ScR2A1R1A3S65R2A1S6S48S53R4S43A2S53R4S42A2M0A2S47G0S49Z2Z1aA2A2A2F_;F_;FF;Frho;").
Proof using .
  intros rho F HF (C1 & C2 & C3).
  pose proof (holds_mem rho F _ HF C1) as H1. rewrite h_ult in H1.
  pose proof (holds_mem rho F _ HF C2) as H2. rewrite h_ule in H2.
  pose proof (holds_mem rho F _ HF C3) as H3. rewrite h_ule, uval_lit in H3 by lia.
  change (2 ^ 26) with 67108864. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S20S0S7S16S26Q40A1A1S22S27S8ScR3A1SbS1R4A1A1A3VTR;S1fS1eR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S22S22S22S23R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S22OS22S23R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S20S20S0S0S32S16SeA1M0S16S1aS0S34A2M1A1S16S1aSaSaA2M2A1S22S7S16S26Q40A1A1M3G2S2aG2R1R5A3S2aG2R2S4RbA1A3F_;Fr;S5S1cG0A1S33RaR9R8A3S1bG0R7A2A3S5S17S38RbRaR9R8S28G1S0S1dS0S34A2R7A4A5S18A3S7G3VTR;S1fS1eRfRdR2R1A5S37S1eS9S1RdA1A1R2R1RaA5A2Ftp1;Frho1;S16S2fA1M4S3aS2eS21S1eR9R8R10S19G4S3bR3S3cR2R1A2A4A5R13RaR9R4R2A4R13S31S30RbRfS29R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S0S34G4S3aS2eS7G3G4S3aS2eS2aG1S19S0S34RaR9A4R14A3S21S1eR12R11R19S19G4S3bR9S3cR8R7A2A4A5R1cR13R12RaR8A4S51S9S1R1aA1A1S31S30R14R18S29R9R13RaA3A3R19A2R8A3S21S1eR9R8ReS19G4S3bR7S3cR6R5A2A4A5ReS31S30R16R1aS29RbR15RcA3A3R1bA2R15RaR9R8R6A6S6S69R17S29RcR16RdA3R1bR1cR1dR10R1eR19RbA9S7S52R18S29RdR17ReA3R1cR1dS1R1eA1S1R1fA1S1R11A1R1RcA9VTR;S1fS1eS36R11S31S30R19R1dS29ReR18RfA3A3R1eA2R18RdRcA5S6aR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1fS1eR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Definition pure_ruleL (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S0S32S16SeA1M0S7S16S26Q40A1A1S6eS22S5S1cG0A1S33R7VPre;R6A3S1bG0R5A2A3S5S17S35R8VPre;R7R6S28S2S0S3VPosts;A4A5S18A3S5S17S73S3eS9S1R9A1A1A2S18A3S5S17S6dS9S1RaA1A1R5A2S18A3S5S17S2cS8S14S9S1RbA1M1A1A1SbG1A1A3S18A3S2S7S2aS2R2VPosts;A3SdS9S1RfA1A1RcR2A3VTR;S1fS1eVJAv;RbA1S68SbS1R10A1A1S39RfVPre;S3R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S1fS1eVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis PURE_da : pure_ruleL Pre_da Posts_da.

Lemma site_da : ltac2:(tb__ "0|1|
S0S0S0S0S0S7S16S26Q40A1A1S22S62R8R7R6R5R4A5S7S27S8ScR5A1SbS1R9A1A1A3SdS9S1RaA1A1R6R2A3VTR;S1fS1eVJAv;S3dA1M0R8R3R6A5R5A2F_;F_;Frho';VTR;S1fS1eG0RaR5R4A5R3A2F_;F_;FQ;Ftp;Frho;FT;FB;FT0;FEc;FE0;").
Proof using TR_facts TR_pre PURE_da.
  intros E0 Ec T0 B T rho tp Q (Cxf & Cok & Cnp & Cnb & Cfb & CT0 & CB & CT & _) HK.
  destruct (da_ok_ent Ec Cok) as [Cent Cchk].
  apply (TR_pre (SPA segs (JAv ndA1) Ec rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) (xf_da E0) rho E0 Ec tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_da Ec (s_da Ec) (R_da Ec) rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_da] in HL. destruct HL as [<-|[]]. cbn [la_state].
  change (ax_add_facts (ss_facts (ax_S Ec)) (import_postA (s_da Ec) Pre_da P_da Ec (R_da Ec))) with (T_da0 Ec). rewrite CT0.
  apply (TR_pre (SPA segs (JAv ndA1) T rho' tp)).
  { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_da T0) rho' T0 B tp w CB Hw). }
  exact (HK rho' HF Hag).
Qed.

Lemma V_B_agree_n : ltac2:(tb__ "0|0|
S25S7S7S5S17S6fR3S4cA2S18A3S51R4R3R2A3S25S2aS25R1S4cA3S5S26Q40A1S13R5R2A2S13R6R2A2A3F_;Fv;F_;F_;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' HV [HA _] v Hv. symmetry. apply HA. pose proof (proj1 (forallb_forall _ _) HV v Hv) as X. apply Pos.ltb_lt in X. exact X.
Qed.

Hypothesis PURE_sd : pure_ruleL Pre_sd Posts_sd.
Lemma site_sd : ltac2:(tb__ "0|4|
S0S0S0S7S16S26Q40A1A1S22S60R6R5R4A3S5S17S2cS8S14S9S1R6A1M0A1A1SbG0A1A3S18A3M1G1S7S27S8ScR7A1SbS1RaA1A1A3SdS9S1RbA1M2A1R8R2A3VTR;S1fS1eVJAv;S3dA1M3RbR3R8A5R7A2F_;F_;Frho';S7S27S8ScR8A1SbG2A1A3SdS9S1RcA1A1R9R2A3VTR;S1fS1eG3RbR3R9A5R8A2F_;F_;Frho';VTR;S1fS1eG3RbR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;FTy;FTn;FE;").
Proof using TR_facts TR_pre PURE_sd.
  intros E Tn Ty rho tp Q (Cok & Cnp & Cnb & Cfb & Ccn & Ccy & CTn & CTy & _) Hbn Hby Kn Ky.
  destruct (sd_ok_ent E Cok) as [Cent Cchk].
  apply TR_facts. intros HF.
  apply (PURE_sd E (s_sd E) (R_sd E) rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_sd] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - change (ax_add_facts (ss_facts (ax_S E)) (import_postA (s_sd E) Pre_sd P_none E (R_sd E))) with (T_sd0 E P_none).
    apply (TR_pre (SPA segs (JAv ndA1) Tn rho' tp)); [|exact (Kn rho' HF Hag)].
    intros w Hw. rewrite <- CTn. apply (SPA_refacts_JA segs (JAv ndA1) rho' (T_sd0 E P_none) _ tp w Hw).
    + rewrite <- CTn in Hbn. exact Hbn.
    + intros tr md _ HF1. apply Forall_app. split; [constructor; [exact (cur_ok_holds E _ rho' Ccn HF1) | constructor] | exact HF1].
  - change (ax_add_facts (ss_facts (ax_S E)) (import_postA (s_sd E) Pre_sd P_num E (R_sd E))) with (T_sd0 E P_num).
    apply (TR_pre (SPA segs (JAv ndA1) Ty rho' tp)); [|exact (Ky rho' HF Hag)].
    intros w Hw. rewrite <- CTy. apply (SPA_refacts_JA segs (JAv ndA1) rho' (T_sd0 E P_num) _ tp w Hw).
    + rewrite <- CTy in Hby. exact Hby.
    + intros tr md _ HF1. apply Forall_app. split; [constructor; [exact (cur_ok_holds E _ rho' Ccy HF1) | constructor] | exact HF1].
Qed.

Lemma entry_hv : ltac2:(tb__ "0|1|
S7S16S26Q40A1A1S22S5S17S66VXGL;SbS1S40A1A1S4dZ4Z12S4S40A1A6S18A3S7SdS9S1S41A1A1R5R1A3VTR;S1fS1eVJAv;S3dA1M0S59R2R5A5R4A2F_;Frho';VTR;S1fS1eG0S40R5R4A5R3A2F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_pre TR_exw TR_pureP.
  intros rho tp Q CXR HK.
  pose proof hv_checks_entry as (C1 & C2 & C3 & C4 & C5 & _ & C7 & C8 & C9 & C10 & C11 & _).
  apply (TR_pre (fun w => exists rho', agree_below (ss_next (ax_S K_hv0)) rho rho' /\ SPA segs (JAv ndA1) K_hv0c rho' tp w)).
  { intros [tr [ms md]] Hw.
    assert (Hw1 : SPA segs (JAv ndA1) K_hv0 rho tp (tr, mkCfg ms md)).
    { rewrite <- C1.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL (bdA A1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 18 E_hv0 (ax_X E_hv0) rho tp _ frL_0 ltac:(lia) C2 ltac:(lia)
               ltac:(change (fs_frame_size 5) with 2048; lia) C3 (fun r H => H) ltac:(rewrite C1; exact C4)); [|exact Hw].
      intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      - exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR C7 lines_in_tvL C5).
      - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tvL (ax_X E_hv0) rho3 tp3 md3 4 18 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR). }
    assert (Hst : forall n, (ss_next (ax_S K_hv0) <= n)%positive -> stableA segs n (JAv ndA1)).
    { intros n Hn. apply (stableA_mono segs (ss_next (ax_S K_hv0)) n _ Hn).
      apply (stableA_JA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA _ ndA1); [apply Pos.leb_le; exact C10 | exact C11]. }
    destruct (SPA_add_cells8 segs nums_mat (JAv ndA1) rho tp K_hv0 i_nums tr ms md Hst C8 Hw1) as (rho' & Hag & Hw2).
    exists rho'. split; [exact Hag|]. rewrite <- C9. exact Hw2. }
  apply TR_exw. intros rho'.
  apply (TR_pureP _ (agree_below (ss_next (ax_S K_hv0)) rho rho')); [intros w [H _]; exact H|]. intros Hag.
  apply (TR_pre (SPA segs (JAv ndA1) K_hv0c rho' tp)); [intros w [_ Hw]; exact Hw|]. exact (HK rho' Hag).
Qed.
End X.
End Sum.
