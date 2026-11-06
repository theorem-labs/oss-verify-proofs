(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "app"; "prod"; "pair"; "Some"; "nil"; "option"; "nat"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sv"; "ss_facts"; "sprop"; "SVar"; "SLit"; "sobj"; "holds"; "cell"; "sstate"; "DUnknown"; "SAlu"; "eval"; "ob_base"; "ob_cells"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "odefault"; "rw"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_below"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "T3"; "X_bodyN"; "datasA"; "t_d"; "t_k"; "O_dataA"; "v_acol"; "v_av"; "v_avn"; "v_avt"; "v_avtw"; "v_avw"; "v_co"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_rp"; "v_sg"; "v_sh"; "v_tr"; "v_ts"; "vecs"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tblL"; "ldef"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk"; "ENDOW"; "tv1"; "PhiP0"; "PhiP1"; "bdLand_a1"; "bdLand_b1"; "add_objs"; "add_objs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ANone"; "PTrue"; "JA"; "JA_pre"; "amode"; "nd_tv"; "ndesc"; "ok_frameKA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "in_ranges"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land"; "E_blr"; "tv_site"; "K0a"; "K0b"; "K1a"; "K1b"; "R_blr"; "E_blr0"; "T_blr0"; "T_blr1"; "XkB"; "s_landA"; "s_landAE"; "s_landBE"; "XR_after0"; "XR_after1"; "XR_body0"; "XR_body1"; "s_blr"; "s_landB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vF"; "vOUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "ndLE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_pf.Sum"; "emp_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xrs_okF"; "xrs_inclb"; "@LinuxProcessSemantics.LinuxProcessSem.Run";
"config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"; "K_afterE"; "X_bodyE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk2"; "bdLand_a0"; "bdLand_b0"; "bd_bli"; "xfb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_pf.BLRP"; "P0_blr"; "PDk_blr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "fnodup"; "vARn"; "xnodup"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_pf.BLR"; "Pre_blr"; "nd_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjJVAy TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueC ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_build_line_index_rom_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_land Lib_load_obj_land_chk Lib_load_obj_land_chk2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
SbaS10S4S30Q40A1A1S95OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc1S3VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2eSbbVCST;R1A2S1S66Z0R2A2S68R2SbcA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2eSbbVXGL;R1A2S1S66Z0R2A2S68R2SbcA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S9S9S2eS2eA2S2eA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable PA : AA -> Prop.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S10OFr;") := ltac2:(tb__ "0|0|
Sc9VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S60VAInv;VCST;VXGL;S8dVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S71VAInv;VCST;VXGL;S8dVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;VPhi;Vnd;Ad").

Hypothesis HXlits : ltac2:(tb__ "0|0|
S2eSc6R1A1SbbVXGL;R2A2F_;Fa;").

Hypothesis HPAany : ltac2:(tb__ "0|0|
SbaSbaVPA;R2A1S5fR2A1VPA;R3A1F_;F_;FA';FA;").

Lemma SPA_zsub : ltac2:(tb__ "0|2|
S2cS10S28S28S1aS28SeS2eSeS4S19A1S4S30Q40A1A1S86S0SdS28A1M0Sb5RaS7Sb6Sb8R6S16R5A1A2ScSb6A1M1A3A2SbS28R9A2A3S0SdS1aA1Sd0S27RaA1R5R4A3SbS1aR9A2A3S0S5S26RaA1S6A3S0G0Sb5S2aRcRbA2S7Sb6Sb7R9A1G1A3A2SbS28RaA2A3S2bS3R10ReRfR6R5A6S2bS3R11RcR10R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fcs;Fj;Fmid;Fi;FA3;FS2;FA1;FA;Frho;FJ;").
Proof.
  intros J rho A A1 S2 A3 i mid j cs tp w H1 H2 Hwf H3 Hw.
  apply (SPA_axforms segs J [AXMerge i] rho (ax_setS A1 S2) A3 tp w H3).
  apply (SPA_zero_cells segs J rho A1 j cs S2 tp w H2 Hwf).
  exact (SPA_axforms segs J [AXSplit i (SLit mid)] rho A A1 tp w H1 Hw).
Qed.

Definition emp_at (rho : valuation) (o : sobj) : Prop := ltac2:(tb__ "0|2|
S1S0S4S19A1S1fVo;A1ScS19A1A3S1S0S23S20Vo;A1S1bA3S1S0S2eS21Vrho;Vo;A2S22Vrho;Vo;A2M0A3S1S66Z0S67S31Q40S1dVrho;S1eVo;A1A2A2G0A2M1A2S66G1S69Z2Z40A2A2A2A2A2A2").
Lemma SPA_add_objs : ltac2:(tb__ "0|0|
S2cS10S4S17A1S28S4S30Q40A1A1S86S0S5S5cR3R4A2S6A3S8aS17S98R6A1R5A3S2bS3R8R5R7R4R3A6S2bS3R9S5bR6R7A2R8R5R4A6F_;F_;F_;Fw;Ftp;FA;Fds;Frho;FJ;").
Proof.
  intros J rho ds. induction ds as [|o r IH]; intros A tp w Hwf Hemp Hw; [exact Hw|]. cbn [add_objs].
  cbn [add_objs_wf] in Hwf. apply andb_prop in Hwf as [Hwf H3]. apply andb_prop in Hwf as [H1 H2].
  apply Forall_cons_iff in Hemp as [(E1 & E2 & E3 & E4) Hemp].
  apply (IH _ tp w H3 Hemp). apply (SPA_add_empty segs J rho A o tp w H1 E1 E2 H2); [|exact Hw]. intros _. split; [exact E3 | exact E4].
Qed.
Lemma emp_data : ltac2:(tb__ "0|1|
S10S38S2eS1S68Z0M0R1A2S68R1Z1000A2A2S0S2eS33R4S3bR3A1A2G0A3S0S2eS33R5S3cR4A1A2G0A3S98R6S3dR5R4A2A2F_;F_;F_;Fe;Ft;Frho;").
Proof.
  intros rho t e He Hd Hk. unfold emp_at, O_dataA, obj_hi_of, obj_lo_of. cbn [ob_cells ob_dflt ob_hi ob_lo ob_base].
  split; [reflexivity|]. split; [reflexivity|]. rewrite soff_lit_small by lia.
  pose proof (uval_range rho (t_k t)) as Rk.
  assert (EK : uval rho (kb e (t_k t)) = e * uval rho (t_k t)). { unfold kb. apply uval_mul_lit; [lia|]. rewrite Hk. lia. }
  split.
  - unfold soff. rewrite bv_signed_U. change (bv_unsigned (eval rho (kb e (t_k t)))) with (uval rho (kb e (t_k t))). rewrite EK, Hk.
    rewrite Z.mul_0_r. reflexivity.
  - change (bv_unsigned (eval rho (t_d t))) with (uval rho (t_d t)). rewrite Hd. lia.
Qed.
Lemma datas_emp : ltac2:(tb__ "0|1|
S10S50S38S93S38R1S7S38S3fR2A1S7S38S43R2A1S7S38S40R2A1S7S38S41R2A1S7S38S42R2A1S7S38S3eR2A1S7S38S4dR2A1S7S38S48R2A1S7S38S45R2A1S7S38S49R2A1S7S38S4cR2A1S7S38S47R2A1S7S38S46R2A1S7S38S4aR2A1S7S38S44R2A1S7S38S4bR2A1S7S38S4eR2A1S7S38S4fR2A1ScS38A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S1S0S2eS33R4S3bR2A1A2Z0M0A3S0S2eS33R4S3cR2A1A2G0A3A2F_;Ft;S8aS17S98R3A1S3aR2A1A3F_;Fv;Frho;").
Proof.
  intros rho v H. unfold datasA.
  repeat (apply Forall_cons; [apply emp_data; [lia | match goal with |- uval _ (t_d ?t) = 0 => apply (proj1 (H t ltac:(cbn; tauto))) end
                                                     | match goal with |- uval _ (t_k ?t) = 0 => apply (proj2 (H t ltac:(cbn; tauto))) end] |]). apply Forall_nil.
Qed.

Lemma datas_emp_land : ltac2:(tb__ "0|0|
S10S6dS2fS93S2fR1S8bSeS2fSc3S8cU190U36A2A4A3S0S12S6fR3R2A2S16Z0A1A3F_;Fx;S8aS17S98S6bR3R2A2A1S3aS51A1A3F_;Fs;Frho;").
Proof.
  intros rho s Hs. apply datas_emp. intros t Ht.
  assert (Z0 : forall x : positive, In x (map Pos.of_nat (seq 400 54)) -> uval (rho_sub rho s) (SVar x) = 0).
  { intros x Hx. unfold uval. rewrite <- eval_subst. cbn [sv_subst]. rewrite (Hs x Hx). apply (uval_lit rho 0). lia. }
  cbn in Ht. unfold vsP, t3 in Ht.
  repeat (destruct Ht as [<-|Ht]; [split; apply Z0; lazy; tauto|]). destruct Ht.
Qed.

Lemma land_bodyN : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S86S0S5S35S11S27S77A1M0A1R4A2S6A3S0S5S70S13G0A1S5aR5A3S6A3S58R5A1S2bS3VJAv;S5dS56S52S8S34R7S55A3S5eA4A1S83R6R5R4A6S1S53S6bR7S85A2M1A1S2bS3VJAFv;S53S90A2S39G1R6R5A6A2F_;F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud HPhi Hw.
  pose proof pipe_b1 as (Pr1 & Pr2 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_b1 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_b1 rho (ax_setS XR_body1 Rt_b1) C9_b1 tp w P1 (SPA_retile segs _ rho XR_body1 _ _ _ Rt_b1 tp w Pr1 Pr2 Hw)) as Hw1.
  pose proof (SPA_zsub _ rho C9_b1 Za1_b1 Zs1_b1 C10_b1 _ _ _ _ tp w P2 P3 P4 P5 Hw1) as Hw2.
  pose proof (SPA_zsub _ rho C10_b1 Za2_b1 Zs2_b1 C11_b1 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_b1 Za3_b1 Zs3_b1 C12_b1 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_b1 Za4_b1 Zs4_b1 C13_b1 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_b1 frL (bd0 ++ ENDOW) K1b rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_b1) tvLand_b1 frL (bd0 ++ ENDOW) ANone K1b rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_b1 frL bd0 K1b rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndA1) M_bodyN (rho_sub rho s_landB) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K1b M_bodyN s_landB (NDA tvLand_b1 frL bd0 (AHead (SLit 0) true)) ndA1 rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K1b)) (bd_subst s_landB (nd_bd ndA1)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndA1) X_bodyN (rho_sub rho s_landB) tp w).
  { rewrite <- (proj1 add_datas_b1). apply (SPA_add_objs _ _ (datasA vsP) M_bodyN tp w (proj2 add_datas_b1)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  assert (HT : tblL (rho_sub rho s_landB)).
  { destruct HPhi as [(T & H1 & H2 & H3) HP0].

    split.
    2: { intros z Hz. assert (ED' : uval (rho_sub rho s_landB) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
         assert (EK' : uval (rho_sub rho s_landB) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
         change (rm (rho_sub rho s_landB)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz). }
    exists T.
    assert (ED : uval (rho_sub rho s_landB) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EC : uval (rho_sub rho s_landB) xLC = uval rho iC) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EL : uval (rho_sub rho s_landB) vLEN = uval rho vLEN) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EI : uval (rho_sub rho s_landB) pI = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landB pI) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EN : uval (rho_sub rho s_landB) pNX = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landB pNX) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EM : rm (rho_sub rho s_landB) = rm rho) by reflexivity.
    rewrite ED, EC, EL, EI, EN, EM. split; [exact H2|]. split; [exact H3|]. split; [exact H1|].
    intros p Hp. exact (proj1 (proj1 H3 0%nat p Hp)). }
  split; [exact HT|]. apply SPA_JAF_intro; [exact Hw10 | exact HT].
Qed.

Lemma land_after0 : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S86S0S5S35S11S27S76A1M0A1R4A2S6A3S0S5S70S13G0A1S59R5A3S6A3S58R5A1S2bS3VJAv;S5dS56S52S8S34R7S55A3S5eA4A1S81R6R5R4A6S1S53S6bR7S7dA2M1A1S2bS3VJAFv;S53S90A2Sa8G1R6R5A6A2F_;F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud HPhi Hw.
  pose proof pipe_a1 as (Pr1 & Pr2 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_a1 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_a1 rho (ax_setS XR_after1 Rt_a1) C9_a1 tp w P1 (SPA_retile segs _ rho XR_after1 _ _ _ Rt_a1 tp w Pr1 Pr2 Hw)) as Hw1.
  pose proof (SPA_zsub _ rho C9_a1 Za1_a1 Zs1_a1 C10_a1 _ _ _ _ tp w P2 P3 P4 P5 Hw1) as Hw2.
  pose proof (SPA_zsub _ rho C10_a1 Za2_a1 Zs2_a1 C11_a1 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_a1 Za3_a1 Zs3_a1 C12_a1 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_a1 Za4_a1 Zs4_a1 C13_a1 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_a1 frL (bd0 ++ ENDOW) K1a rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_a1) tvLand_a1 frL (bd0 ++ ENDOW) ANone K1a rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_a1 frL bd0 K1a rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndA1) M_after0 (rho_sub rho s_landA) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K1a M_after0 s_landA (NDA tvLand_a1 frL bd0 (AHead (SLit 0) true)) ndA1 rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K1a)) (bd_subst s_landA (nd_bd ndA1)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndA1) K_after0 (rho_sub rho s_landA) tp w).
  { rewrite <- (proj1 add_datas_a1). apply (SPA_add_objs _ _ (datasA vsP) M_after0 tp w (proj2 add_datas_a1)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  assert (HT : tblL (rho_sub rho s_landA)).
  { destruct HPhi as [(T & H1 & H2 & H3) HP0].

    split.
    2: { intros z Hz. assert (ED' : uval (rho_sub rho s_landA) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
         assert (EK' : uval (rho_sub rho s_landA) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
         change (rm (rho_sub rho s_landA)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz). }
    exists T.
    assert (ED : uval (rho_sub rho s_landA) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EC : uval (rho_sub rho s_landA) xLC = uval rho iC) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EL : uval (rho_sub rho s_landA) vLEN = uval rho vLEN) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EI : uval (rho_sub rho s_landA) pI = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landA pI) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EN : uval (rho_sub rho s_landA) pNX = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landA pNX) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EM : rm (rho_sub rho s_landA) = rm rho) by reflexivity.
    rewrite ED, EC, EL, EI, EN, EM. split; [exact H2|]. split; [exact H3|]. split; [exact H1|].
    intros p Hp. exact (proj1 (proj1 H3 0%nat p Hp)). }
  split; [exact HT|]. apply SPA_JAF_intro; [exact Hw10 | exact HT].
Qed.

Lemma land_bodyE : ltac2:(tb__ "0|1|
S4S34A1S10S4S30Q40A1A1S86S0S5S35S11S27S75A1M0A1R4A2S6A3S0S5S70S13G0A1SacR5A3S6A3S2bS3VJAv;S5dS56S52S8S34R6S55A3S5eA4A1S82R5R4R3A6S2bS3VJAv;S91A1SaaS6bR6S7fA2R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud Hw.
  pose proof pipe_b0 as (Pr1 & Pr2 & P1 & Q1 & P2 & P3 & P4 & P5 & Q2 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_b0 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_b0 rho (ax_setS XR_body0 Rt_b0) C9_b0 tp w P1 (SPA_retile segs _ rho XR_body0 _ _ _ Rt_b0 tp w Pr1 Pr2 Hw)) as Hw1.
  pose proof (SPA_axforms segs _ [AXSplit i96_b0 (SLit 104)] rho C9_b0 D1_b0 tp w Q1 Hw1) as Hw1b.
  pose proof (SPA_zsub _ rho D1_b0 Za1_b0 Zs1_b0 D2_b0 _ _ _ _ tp w P2 P3 P4 P5 Hw1b) as Hw1c.
  pose proof (SPA_axforms segs _ [AXMerge i96_b0] rho D2_b0 C10_b0 tp w Q2 Hw1c) as Hw2.
  pose proof (SPA_zsub _ rho C10_b0 Za2_b0 Zs2_b0 C11_b0 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_b0 Za3_b0 Zs3_b0 C12_b0 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_b0 Za4_b0 Zs4_b0 C13_b0 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_b0 frL (bd0 ++ ENDOW) K0b rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_b0) tvLand_b0 frL (bd0 ++ ENDOW) ANone K0b rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_b0 frL bd0 K0b rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndLE) M_bodyE (rho_sub rho s_landBE) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K0b M_bodyE s_landBE (NDA tvLand_b0 frL bd0 (AHead (SLit 0) true)) ndLE rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K0b)) (bd_subst s_landBE (nd_bd ndLE)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndLE) X_bodyE (rho_sub rho s_landBE) tp w).
  { rewrite <- (proj1 add_datas_b0). apply (SPA_add_objs _ _ (datasA vsP) M_bodyE tp w (proj2 add_datas_b0)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  exact Hw10.
Qed.

Lemma land_afterE : ltac2:(tb__ "0|1|
S4S34A1S10S4S30Q40A1A1S86S0S5S35S11S27S74A1M0A1R4A2S6A3S0S5S70S13G0A1SabR5A3S6A3S2bS3VJAv;S5dS56S52S8S34R6S55A3S5eA4A1S80R5R4R3A6S2bS3VJAv;S91A1Sa9S6bR6S7eA2R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud Hw.
  pose proof pipe_a0 as (Pr1 & Pr2 & P1 & Q1 & P2 & P3 & P4 & P5 & Q2 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_a0 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_a0 rho (ax_setS XR_after0 Rt_a0) C9_a0 tp w P1 (SPA_retile segs _ rho XR_after0 _ _ _ Rt_a0 tp w Pr1 Pr2 Hw)) as Hw1.
  pose proof (SPA_axforms segs _ [AXSplit i96_a0 (SLit 104)] rho C9_a0 D1_a0 tp w Q1 Hw1) as Hw1b.
  pose proof (SPA_zsub _ rho D1_a0 Za1_a0 Zs1_a0 D2_a0 _ _ _ _ tp w P2 P3 P4 P5 Hw1b) as Hw1c.
  pose proof (SPA_axforms segs _ [AXMerge i96_a0] rho D2_a0 C10_a0 tp w Q2 Hw1c) as Hw2.
  pose proof (SPA_zsub _ rho C10_a0 Za2_a0 Zs2_a0 C11_a0 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_a0 Za3_a0 Zs3_a0 C12_a0 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_a0 Za4_a0 Zs4_a0 C13_a0 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_a0 frL (bd0 ++ ENDOW) K0a rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_a0) tvLand_a0 frL (bd0 ++ ENDOW) ANone K0a rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_a0 frL bd0 K0a rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndLE) M_afterE (rho_sub rho s_landAE) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K0a M_afterE s_landAE (NDA tvLand_a0 frL bd0 (AHead (SLit 0) true)) ndLE rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K0a)) (bd_subst s_landAE (nd_bd ndLE)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndLE) K_afterE (rho_sub rho s_landAE) tp w).
  { rewrite <- (proj1 add_datas_a0). apply (SPA_add_objs _ _ (datasA vsP) M_afterE tp w (proj2 add_datas_a0)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  exact Hw10.
Qed.

Lemma land_after0_cnt : ltac2:(tb__ "0|2|
S10S1S0S2eS33S6bR1S7dA2M0S15P191A1A2Z0M1A3S0S2eS33G0S15P19aA1A2G1A3A2Frho;").
Proof.
  intros rho. pose proof land_checks_a1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cz).
  assert (Z0 : forall x : positive, In x (map Pos.of_nat (seq 400 54)) -> uval (rho_sub rho s_landA) (SVar x) = 0).
  { intros x Hx. unfold uval. rewrite <- eval_subst. cbn [sv_subst]. rewrite (sv_eqb_sound _ _ (proj1 (forallb_forall _ _) Cz x Hx)). apply (uval_lit rho 0). lia. }
  split; apply Z0; lazy; tauto.
Qed.
Lemma land_ldefBE : ltac2:(tb__ "0|0|
S10S57R1A1S54S6bR2S7fA2A1F_;Frho;").
Proof.
  intros rho HP0 z Hz.
  assert (ED' : uval (rho_sub rho s_landBE) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (EK' : uval (rho_sub rho s_landBE) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
  change (rm (rho_sub rho s_landBE)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz).
Qed.
Lemma land_ldefAE : ltac2:(tb__ "0|0|
S10S57R1A1S54S6bR2S7eA2A1F_;Frho;").
Proof.
  intros rho HP0 z Hz.
  assert (ED' : uval (rho_sub rho s_landAE) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (EK' : uval (rho_sub rho s_landAE) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
  change (rm (rho_sub rho s_landAE)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz).
Qed.

Lemma site_factsZ : ltac2:(tb__ "0|4|
S10S8aS14S18R1A1S13S27S72A1A1A3S1S66S67S31Q40S24R2SbeA2A2M0Z1a80A2S33R2S15PaA1A2M1A2S1S66G1Z800000000000M2A2S1S66G0S33R2S8fA2M3A2S1S66S67G3Z110A2G2A2S66S67S33R2S8eA2Z800A2Z7fffff800000A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HF.
  factz HF (SPUle (SAlu ALU_ADD (SVar 30) (SLit 6784)) (SVar 10)) H1. factz HF (SPUle (SVar 10) (SLit 140737488355328)) H2.
  factz HF (SPUle (SVar 30) vOUT) H3. factz HF (SPUle (SAlu ALU_ADD vOUT (SLit 272)) (SLit 140737488355328)) H4.
  factz HF (SPUle vF (SLit 140737479964672)) H5. factz HF (SPUle vOUT (SLit 140737488355328)) H6. factz HF (SPUle (SVar 30) (SLit 140737479966720)) H7.
  rewrite uval_lit in H2 by lia. rewrite uval_lit in H4 by lia. rewrite uval_lit in H5 by lia. rewrite uval_lit in H6 by lia. rewrite uval_lit in H7 by lia.
  pose proof (uval_range rho (SVar 30)) as R30. pose proof (uval_range rho vOUT) as RO. pose proof (uval_range rho (SVar 10)) as R10.
  rewrite uval_add_small in H4 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H4 by lia.
  rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *. repeat split; lia.
Qed.

Lemma pclMA_x : ltac2:(tb__ "0|0|
S10S4S9S12S12A2A1S4S9S9S12S2eA2S12A2A1S2eSa2VCST;Vrho0;VFB;VFF;R1A5Sa2VCST;Vrho0;Sa0VFB;R5R4A3Sa1VFF;R5R3A3R2A5F_;Fa;Ffr;Ftv;Frho;").
Proof.
  intros rho tv fr a H. apply (pclMA_mono CST rho0 FB _ FF _ a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx | exact H].
Qed.
Lemma f5_pclMA : ltac2:(tb__ "0|1|
S10S4S9S12S12A2A1S2eS1S66S33R3S8eA2M0R1A2S68R1S67G0Z800A2A2A2Sa2VCST;Vrho0;Sa0VFB;R4R3A3Sa1VFF;R4S52A3R2A5F_;Fa;Ftv;Frho;").
Proof.
  intros rho tv a Ha. right; right; right. exists (uval rho vF), 2048, (uval rho vFL). split; [|exact Ha].
  apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity|]. reflexivity.
Qed.
Lemma ar_pclMA : ltac2:(tb__ "0|1|
S10S4S9S9S12S2eA2S12A2A1S2eS2S0S2eS33R3Sb2A2Z0A3A1S1S66S33R4Sb2A2M0R2A2S68R2S67G0Z40A2A2A2Sa2VCST;Vrho0;Sa0VFB;R5S73A3Sa1VFF;R5R4A3R3A5F_;F_;Fa;Ffr;Frho;").
Proof.
  intros rho fr a Hnz Ha. right; right; left. exists (uval rho vARn), 64. split; [|exact Ha].
  apply In_FBx. right. exists blkAR. split; [left; reflexivity|]. split; [unfold tnz, blkAR; cbn [fst]; unfold uval in Hnz; exact Hnz|].
  unfold tvv, blkAR. cbn [fst snd]. unfold uval. rewrite U_lit. reflexivity.
Qed.

Lemma uval_spm6784 : ltac2:(tb__ "0|2|
S10S66Z1a80M0S33R1S15PaA1M1A2A2S0S2eS33R2S1cSc4G1S16N1a80A1A3A2S6aS33R2G1A2G0A2A3F_;Frho;").
Proof.
  intros rho Hk. unfold uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + -6784) with (x - 6784) by lia. apply Z.mod_small. lia.
Qed.
Ltac in_lits_tac := unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.in_lits; cbn -[Z.add Z.le Z.lt]; repeat match goal with |- _ \/ _ => first [left; lia | right] end; lia.

Lemma HIN_RX : ltac2:(tb__ "0|0|
S10S8aS14S18R1A1S13S27S72A1A1A3VP0;Vrho0;A1S99S8dVrho0;R3A3S1Sa3VCST;Vrho0;VFB;VFF;R4S73S52S78A8Sa4VCST;VXGL;Vrho0;VFB;VFF;R4S73S52S7cA9A2F_;F_;F_;Frho;").
Proof.
  intros rho HF HP0 Hav. destruct (site_factsZ rho HF) as (Zsp & Zsp47 & Zo & Zo47 & ZF).
  pose proof (T0_agreeA rho0 NP rho Hav eq_refl) as ET. destruct HP0 as (Ptxt & Pcfg & Plnk).
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  pose proof (uval_range rho vF) as RF. pose proof (uval_range rho vARn) as RA. pose proof (uval_range rho (SVar 28)) as R28. pose proof (uval_range rho vCFGp) as R15.
  factz HF (SPUle (SLit IMG_HI) vARn) HAnz. unfold IMG_HI in HAnz. rewrite uval_lit in HAnz by lia.
  pose proof (uval_range rho (SVar 30)) as R30. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in R30. pose proof (uval_range rho (SVar 10)) as R10.
  assert (STK : forall a, bv_unsigned (rw rho V_TOP) <= a < 140737488355328 -> pclMA CST rho0 (FBx FB rho tv_site) (FFx FF rho frL) a).
  { intros a Ha. left. rewrite ET. exact Ha. }
  split.
  - intros o a Ho Hr. unfold R_blr in Ho. cbn in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      unfold obj_range, obj_lo_of, obj_hi_of in Hr; cbn [ob_base ob_lo ob_hi fst snd] in Hr; rewrite ?soff_lit_small in Hr by lia;
      repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in Hr.
    all: first [ apply ar_pclMA; unfold vARn, pAR in *; lia
               | apply f5_pclMA; unfold vF in *; lia
               | apply STK; unfold vOUT in *; lia
               | apply pclMA_x; apply Plnk; rewrite <- (AG 28%positive (SVar 28) eq_refl ltac:(reflexivity)); lia
               | apply pclMA_x; apply Pcfg; rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)); unfold vCFGp in *; lia
               | match goal with H : (_ <= ?a < _) |- pclMA _ _ _ _ ?a => let t := type of H in idtac "ROBJ-LEFT" t end ].
    all: fail.
  - intros r a Hr Ha. unfold XkB in Hr. cbn in Hr.
    repeat (destruct Hr as [Hr|Hr]); try contradiction; subst r; cbn [fst snd] in Ha;
      repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in Ha; rewrite ?uval_lit in Ha by lia.
    all: first [ right; apply HXlits; in_lits_tac
               | lia
               | left; apply pclMA_x; apply Ptxt; rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)); unfold vBUF, vLEN in *; lia
               | left; apply pclMA_x; apply Pcfg; rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)); unfold vCFGp in *; lia
               | left; apply STK; unfold vOUT in *; lia
               | left; apply ar_pclMA; unfold vARn, pAR in *; lia
               | left; apply f5_pclMA; rewrite uval_add_small in Ha by (rewrite uval_lit by lia; unfold vF in *; lia); rewrite uval_lit in Ha by lia; unfold vF in *; lia
               | left; apply STK; rewrite (uval_spm6784 rho) in Ha by lia; lia
               | match goal with H : (_ <= ?a < _) |- _ => let t := type of H in idtac "XRS-LEFT" t end ].
    all: fail.
Qed.
Lemma HIN_blr : ltac2:(tb__ "0|0|
S10S97S8aS14S18R2A1S13S27S72A1A1A3VP0;Vrho0;A1S99S8dVrho0;R4A3S1Sa3VCST;Vrho0;VFB;VFF;R5S73S52S78A8S1Sa4VCST;VXGL;Vrho0;VFB;VFF;R5S73S52S7cA9SafVCST;Sa0VFB;R5S73A3Sa1VFF;R5S52A3S6bS6cR5S78R4A3S84A2A4A2A2F_;F_;F_;Fms;Frho;").
Proof.
  intros rho ms HF HP0 Hav. destruct (HIN_RX rho HF HP0 Hav) as [HR HX]. split; [exact HR|]. split; [exact HX|].
  destruct (site_factsZ rho HF) as (Zsp & Zsp47 & Zo & Zo47 & ZF). destruct HP0 as (Ptxt & Pcfg & Plnk).
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  pose proof (uval_range rho vF) as RF.
  set (r := rho_sub (rho_absorb rho R_blr ms) s_blr).
    assert (EV : forall e, uval r e = uval rho (sv_subst s_blr e)) by (intros e; unfold uval, r; rewrite <- eval_subst, eval_absorb; reflexivity).
    assert (ET0 : TobjJV.T0 r = TobjJV.T0 rho0) by (unfold r; apply (T0_calleeA NP rho0 s_blr rho R_blr ms Hav); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  split; [split|].
  - intros a Ha. rewrite !EV in Ha. change (sv_subst s_blr BLR.vBUF) with vBUF in Ha. change (sv_subst s_blr BLR.vLEN) with vLEN in Ha.
      rewrite (AG 13%positive vBUF eq_refl ltac:(reflexivity)), (AG 14%positive vLEN eq_refl ltac:(reflexivity)) in Ha.
      pose proof (pclMA_x rho tv_site frL a (Ptxt a Ha)) as X. unfold pclMA in X |- *. rewrite ET0. exact X.
  - rewrite EV. change (sv_subst s_blr BLR.vALC) with (SAlu ALU_ADD vF (SLit 368)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
      exists (uval rho vF), 2048, (uval rho vFL). split; [|lia]. apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity].
  - intros z Hz. exfalso. rewrite !EV in Hz. change (sv_subst s_blr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.vDt) with (SLit 0) in Hz. change (sv_subst s_blr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.vK) with (SLit 0) in Hz.
      rewrite !uval_lit in Hz by lia. lia.
Qed.

Lemma Forall_fnodup : ltac2:(tb__ "0|0|
S14OF_;S4S14A1S8aS14R2R1A3S8aS14R3Sb1R2A1A3F_;Fl;FP;").
Proof.
  intros P l H. induction l as [|x r IH]; [constructor|]. cbn [fnodup]. apply Forall_cons_iff in H as [Hx Hr].
  destruct (existsb (sprop_eqb x) r); [exact (IH Hr) | constructor; [exact Hx | exact (IH Hr)]].
Qed.
Lemma SPA_back : ltac2:(tb__ "0|2|
S2cS10S28S28S28S4S30Q40A1A1S86S0SdS28A1Sb5R5SaeR5A1A2SbS28R4A2A3S0S5Sa5Sb3S29R5A1M0A1G0A2S6A3S0S5S94S14S25S11S27R6A1M1A1A1Sb1S13G1A1A1A3S6A3S0S28SccScbR7Sb3S29R7A1A1A2Sb1S13S27R7A1A1A1A2R6A3S2bS3RbR9RaR6R5A6S2bS3RcR8RbR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;FT';FA;FT;Frho;FJ;").
Proof.
  intros J rho T A T' tp w H1 H2 H3 H4 Hw. rewrite <- H4.
  apply (SPA_refacts segs J rho (ax_setX A (xnodup (ax_X A)))); [| exact H3 | intros HF; apply Forall_fnodup; exact HF].
  apply (SPA_x_incl segs J rho A); [exact H2|]. exact (SPA_axforms segs J (xfb T) rho T A tp w H1 Hw).
Qed.

Lemma blk_not_R : ltac2:(tb__ "0|4|
S4S34A1S62S28S10S10S4S30Q40M0A1A1S86S12S12S2bS3VJAv;S5dS7S9S12S12A2M1Sb4S7G1SaS12S12R2R1A4ScG1A1A3A3S52R9R8A4A1R7R5R4R3A6S99S11S27S72A1A1R7R6A3S2S0S2eS33R7R4A2Z0M2A3A1S2S0S2eS33R8Sb2A2G2A3A1Sa3VCST;Vrho0;VFB;VFF;RaS73S52S78A8S2eS1S66S33RbR8A2M3R1A2S68R1S67G3S33RbR7A2A2A2A2S2S6eRdS78S32G0R2A2A3A1F_;Fz;F_;F_;F_;F_;F_;Fn;Fd;Fw;Ftp;Frho';Frho;FS;Fam;Fbd;").
Proof.
  intros bd am S rho rho' tp [tr [ms md]] d n [_ (Ai & kc & HJ)] Hag Hnz HnzA HR z Hz (o & Ho & Hr).
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & _). cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR.
  assert (Hin : In (d, n) [blkAR; (d, n)]) by (right; left; reflexivity). assert (HinA : In blkAR [blkAR; (d, n)]) by (left; reflexivity).
  assert (Hne : tvv rho' (d, n) <> tvv rho' blkAR).
  { destruct HD as [HD1 _]. intros E. apply (HD1 (d, n) ltac:(left; reflexivity)); [unfold tnz, blkAR; cbn [fst]; unfold uval in HnzA; exact HnzA | exact Hnz | symmetry; exact E]. }
  pose proof (uval_range rho' d) as Rd. pose proof (uval_range rho' n) as Rn.
  destruct (proj1 (Forall_forall _ _) HN (d, n) Hin Hnz) as (_ & Hlive & Hnfb). unfold tvv in Hlive, Hnfb. cbn [fst snd] in Hlive, Hnfb.
  assert (Hz64 : 0 <= z < 2 ^ 64).
  { split; [lia|]. destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl & _). destruct (HBl _ _ Hlive) as (_ & _ & _ & G4 & _).
    pose proof (topG_range (aa_geom Ai)). unfold uval in *. lia. }
  pose proof (HR o (bv_unsigned (Z_to_bv 64 z)) Ho Hr) as HP. rewrite U_Z_to_bv in HP by exact Hz64.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho' tp md (FBx FB rho tv_site) (FFx FF rho frL) (bv_unsigned (eval rho' d)) (bv_unsigned (eval rho' n)) z HM).
  -
    intros bn Hbn. apply In_FBx in Hbn as [Hbn|(t & Ht & Htnz & <-)]; [exact (HB _ Hbn)|].
    destruct Ht as [<-|[]]. destruct (proj1 (Forall_forall _ _) HN blkAR HinA HnzA) as (_ & HlA & _).
    replace (tvv rho blkAR) with (tvv rho' blkAR); [exact HlA|]. unfold tvv, blkAR, vARn, pAR. cbn [fst snd eval]. rewrite <- (proj1 Hag 233%positive) by reflexivity. reflexivity.
  - replace (FFx FF rho frL) with (FFx FF rho' frL); [exact (ffinA_FFx FF Ai rho' frL HFF HFR)|].
    unfold FFx, frL, frv, uval, vF, vFL. cbn [map fst snd eval]. rewrite <- (proj1 Hag 110%positive) by reflexivity. rewrite <- (proj1 Hag 120%positive) by reflexivity. reflexivity.
  - exact HT.
  - exact Hlive.
  - intros HinF. apply In_FBx in HinF as [HinF|(t & Ht & Htnz & Et)]; [exact (Hnfb HinF)|]. destruct Ht as [<-|[]].
    apply Hne. unfold tvv in Et |- *. cbn [fst snd] in Et |- *. rewrite <- Et. unfold blkAR, vARn, pAR. cbn [fst snd eval]. rewrite <- (proj1 Hag 233%positive) by reflexivity. reflexivity.
  - unfold uval in Hz. exact Hz.
  - exact HP.
Qed.

Lemma d_nz_of_JAv : ltac2:(tb__ "0|1|
S64S10S4S30Q40A1A1S4S96A1S95S12S12VJAv;R7R6R5R4R3A5S93S9S12S12A2SaS12S12R3Sc5Z10R2A2A4S63R8A1A3S66S33R8R3A2ScaA2S2S0S2eS33R9R4A2Z0M0A3A1S2S0S2eS33RaR6A2G0A3A1F_;F_;F_;F_;Fk;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md d k HJ Hin Hk Hk0 Hd.
  pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 P0 FB FF BX PA nd rho tp tr md (d, kb 16 k) HJ Hin Hd) as Z0.
  cbn [snd] in Z0. change (bv_unsigned (eval rho (kb 16 k))) with (uval rho (kb 16 k)) in Z0.
  unfold kb, B32 in *. rewrite uval_mul_lit in Z0 by lia. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2cS28S10S4S30Q40A1A1S87S8aS14S18R3A1S13S27R4A1A1A3VTR;S2bS3R6R5R4R3A5R2A2M0F_;G0F_;FQa;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Qa : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Qa) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Qa.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S87S87S87S86R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQa;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S87OS87S86R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQa;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2cS2cS28S28S6dS4S17A1M0S4S9S28S9bA2M1A1S4S9S12S12A2M2A1S87S10S4S30Q40A1A1M3G2S93G2R1R5A3S93G2R2S29RbA1A3F_;Fr;S0SdG0A1S9fRaR9R8A3SbG0R7A2A3S0S5S9eRbRaR9R8S8bG1S28SfS28S9bA2R7A4A5S6A3S10G3VTR;S2bS3RfRdR2R1A5S9cS3S11S27RdA1A1R2R1RaA5A2Ftp1;Frho1;S4S96A1M4S97S95S2dS3R9R8R10SaG4Sa6R3Sa7R2R1A2A4A5R13RaR9R4R2A4R13S6bS6cRbRfS92R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S28S9bG4S97S95S10G3G4S97S95S93G1SaS28S9bRaR9A4R14A3S2dS3R12R11R19SaG4Sa6R9Sa7R8R7A2A4A5R1cR13R12RaR8A4S99S11S27R1aA1A1S6bS6cR14R18S92R9R13RaA3A3R19A2R8A3S2dS3R9R8ReSaG4Sa6R7Sa7R6R5A2A4A5ReS6bS6cR16R1aS92RbR15RcA3A3R1bA2R15RaR9R8R6A6S1SceR17S92RcR16RdA3R1bR1cR1dR10R1eR19RbA9S10S9aR18S92RdR17ReA3R1cR1dS27R1eA1S27R1fA1S27R11A1R1RcA9VTR;S2bS3S9dR11S6bS6cR19R1dS92ReR18RfA3A3R1eA2R18RdRcA5ScfR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2bS3R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQa;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CBLR : ltac2:(tb__ "0|1|
S4S9S2eS2eA2M0A1S4S9G0S2eA2A1S37S10S4S30Q40A1A1S36Z5R3A2VTR;S2bS3S61VAInv;VCST;VXGL;VKc;SafVCST;R6R5A3R6R5R4S5fSc8AaSc7R3R2A5S9cS3ScdR3R2Sd1VAInv;VCST;VXGL;VKc;SafVCST;A1S5fSb0R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Variable brest : list bitem.
Variable Q : assn.
Hypothesis CONT1 : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S58R2A1VTR;S2bS3VJAv;S5dS56S52Vbrest;S5eA4A1S7bR3R2A5VQ;A2F_;Ftp';Frho';").
Hypothesis CONT0 : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S57R2A1VTR;S2bS3VJAv;S5dS56S52Vbrest;S5eA4A1S7aR3R2A5VQ;A2F_;Ftp';Frho';").

Lemma X_E_blr : ltac2:(tb__ "0|3|
S4S34A1S10S4S30Q40A1A1S0S5S35S11S27S72A1M0A1M1R3A2S6A3S0S5S35G1Vbrest;A2S6A3Sb9S8dVrho0;VP0;S13G0A1S16Z0M2A1G2R5S8S34SadVbrest;A3A8VTR;S2bS3VJAv;S5dS73S52R6S5eA4A1S79R5R4A5VQ;A2F_;F_;F_;Ftp;Frho;Fbd;").
Proof.
  intros bd rho tp Hbd Hbr HPAY.
  pose proof site_checks as (CXk & Ce & Cchk & Ctp & Cdom & Cnf & Cpass & Cam & Cpd & Cbd & Cx1 & Cx2 & Cx3 & Ctvb & Cfrb & Cit1 & Cit0 & Ci40 & Ci41 & Ci42 & Cj40 & Cj42 & Civ1 & Civ0 & Cs13).

  eapply TR_pre with (P := SPA segs (JAv (NDA (tv_site ++ tv_pass) frL bd ANone)) E_blr rho tp).
  { intros w Hw. rewrite <- Cx3. apply (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv_site tv_pass frL bd); [reflexivity|].
    apply SPA_x_publish_empty; [lia | reflexivity |].
    exact (SPA_axforms segs _ _ rho E_blr1 E_blr2 tp w Cx2 (SPA_axforms segs _ _ rho E_blr0 E_blr1 tp w Cx1 Hw)). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NP rho0 rho)).
  { intros [tr [ms md]] [_ (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. }
  intros [HP0 Hav].
  pose proof (HIN_blr rho) as HIN. pose proof (proj1 (HIN_RX rho HF HP0 Hav)) as HR.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA HKc HBX (BLRP.P0_blr CST) PTrue (fun _ _ => I) HPAany BLR.Pre_blr BLR.nd_pre BLRP.PDk_blr NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CBLR eq_refl
           E_blr s_blr R_blr XkB rho tp tv_site tv_pass frL bd brest ANone Q CXk Ce Cchk Ctp Cdom Cnf).
  - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
  - exact Hbr.
  - exact Cpass.
  - exact Cam.
  - rewrite Cbd. exact HPAY.
  - exact Cpd.
  - intros Ai ms HF' HP0' Hav' HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN ms HF' HP0' Hav').
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK HPSI. cbn [BLRP.PDk_blr In] in Hd.
    pose proof site_checks as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT1 & CT0 & F1k & F1ck & F1a & F0k & F0a).
    pose proof back_checks as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    assert (EL' : uval rho' vLEN = uval rho vLEN) by (unfold uval, vLEN; cbn [eval]; rewrite <- (proj1 Hag 14%positive eq_refl); reflexivity).
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd nd_tv nd_bd nd_am BLR.ndP ND am_subst app] in HPSI |- *;
      destruct HPSI as (r0c & rhoL & HPsi & Hd1 & Hd2 & Hd3).
    +
      rewrite Cit0, CT0. cbn [app].
      apply TR_facts. intros HF2.
      pose proof (holds_mem _ _ _ HF2 F0k) as FkB. pose proof (holds_mem _ _ _ HF2 F0a) as FaI. zf FkB. zf FaI.
      repeat change (bv_unsigned (eval rho' ?e)) with (uval rho' e) in FkB, FaI. unfold B32 in FkB. unfold IMG_HI in FaI. rewrite uval_lit in FkB, FaI by lia.
      assert (E_D : uval rho' iD = uval rhoL (SVar 140)) by (unfold uval; rewrite <- (Hd3 (SVar 140)) by exact (proj1 (andb_prop _ _ Civ0)); rewrite Cj40; reflexivity).
      assert (E_K : uval rho' iK = uval rhoL (SVar 142)) by (unfold uval; rewrite <- (Hd3 (SVar 142)) by exact (proj1 (andb_prop _ _ (proj2 (andb_prop _ _ Civ0)))); rewrite Cj42; reflexivity).
      apply (TR_pureP _ (uval rho' iK <> 0 -> forall z, uval rho' iD <= z < uval rho' iD + uval rho' (kb 16 iK) -> ~ in_ranges rho R_blr (Z_to_bv 64 z))).
      { intros w Hw HK0. destruct w as [tr [ms md]].
        assert (HnzD : uval rho' iD <> 0) by (destruct Hw as [_ HJw]; exact (d_nz_of_JAv _ _ _ _ _ iD iK HJw ltac:(right; left; reflexivity) ltac:(unfold B32; lia) HK0)).
        exact (blk_not_R brest ANone _ rho rho' tp' _ iD (kb 16 iK) Hw Hag HnzD ltac:(lia) HR). }
      intros NR.
      assert (HP : PhiP0 rho').
      { intros z Hz. pose proof (uval_range rho' iK) as RK.
        assert (EK16 : uval rho' (kb 16 iK) = 16 * uval rho' iK) by (unfold kb; apply uval_mul_lit; lia).
        destruct (Z.eq_dec (uval rho' iK) 0) as [K0|Kn0]; [lia|].
        destruct (Hd2 _ (NR Kn0 z ltac:(rewrite EK16; exact Hz))) as [_ E2]. rewrite E2. apply HPsi. rewrite <- E_D, <- E_K. exact Hz. }
      eapply TR_pre; [|exact (CONT0 rho' tp' HP)]. intros w Hw. exact (SPA_back _ rho' T_blr0a Ab0 T_blr0 tp' w B5 B6 B7 B8 Hw).
    +
      rewrite Cit1, CT1. cbn [app].
      apply TR_facts. intros HF2.
      pose proof (holds_mem _ _ _ HF2 F1k) as FkB. pose proof (holds_mem _ _ _ HF2 F1a) as FaI. pose proof (holds_mem _ _ _ HF2 F1ck) as Fck. zf FkB. zf FaI. zf Fck.
      repeat change (bv_unsigned (eval rho' ?e)) with (uval rho' e) in FkB, FaI, Fck. unfold B32 in FkB. unfold IMG_HI in FaI. rewrite uval_lit in FkB, FaI by lia.
      assert (E_D : uval rho' iD = uval rhoL (SVar 140)) by (unfold uval; rewrite <- (Hd3 (SVar 140)) by exact (proj1 (andb_prop _ _ Civ1)); rewrite Ci40; reflexivity).
      assert (E_C : uval rho' iC = uval rhoL (SVar 141)) by (unfold uval; rewrite <- (Hd3 (SVar 141)) by exact (proj1 (andb_prop _ _ (proj2 (andb_prop _ _ Civ1)))); rewrite Ci41; reflexivity).
      assert (E_K : uval rho' iK = uval rhoL (SVar 142)) by (unfold uval; rewrite <- (Hd3 (SVar 142)) by exact (proj1 (andb_prop _ _ (proj2 (andb_prop _ _ (proj2 (andb_prop _ _ Civ1)))))); rewrite Ci42; reflexivity).
      assert (E_L : uval r0c BLR.vLEN = uval rho' vLEN) by (unfold uval; rewrite Hd1; change (sv_subst s_blr BLR.vLEN) with vLEN; symmetry; exact EL').
      apply (TR_pureP _ (uval rho' iK <> 0 -> forall z, uval rho' iD <= z < uval rho' iD + uval rho' (kb 16 iK) -> ~ in_ranges rho R_blr (Z_to_bv 64 z))).
      { intros w Hw HK0. destruct w as [tr [ms md]].
        assert (HnzD : uval rho' iD <> 0) by (destruct Hw as [_ HJw]; exact (d_nz_of_JAv _ _ _ _ _ iD iK HJw ltac:(right; left; reflexivity) ltac:(unfold B32; lia) HK0)).
        exact (blk_not_R brest ANone _ rho rho' tp' _ iD (kb 16 iK) Hw Hag HnzD ltac:(lia) HR). }
      intros NR.
      pose proof (uval_range rho' iK) as RK. pose proof (uval_range rho' iC) as RC.
      assert (EK16 : uval rho' (kb 16 iK) = 16 * uval rho' iK) by (unfold kb; apply uval_mul_lit; lia).
      destruct HPsi as [(T & HT1 & HT2 & HT3) HDEF].
      assert (HP : PhiP1 rho').
      { split.
        - exists T. split; [rewrite E_C; exact HT1|]. split; [|rewrite <- E_L; exact HT3].
          apply (decodes_ext (rm rhoL)); [|rewrite E_D; exact HT2]. intros z Hz.
          destruct (Z.eq_dec (uval rho' iK) 0) as [K0|Kn0]; [lia|].
          destruct (Hd2 _ (NR Kn0 z ltac:(rewrite EK16; lia))) as [_ E2]. exact E2.
        - intros z Hz. destruct (Z.eq_dec (uval rho' iK) 0) as [K0|Kn0]; [lia|].
          destruct (Hd2 _ (NR Kn0 z ltac:(rewrite EK16; exact Hz))) as [_ E2]. rewrite E2. apply HDEF. rewrite <- E_D, <- E_K. exact Hz. }
      eapply TR_pre; [|exact (CONT1 rho' tp' HP)]. intros w Hw. exact (SPA_back _ rho' T_blr1a Ab1 T_blr1 tp' w B1 B2 B3 B4 Hw).
Qed.
End X.

Section Pack.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S65S3VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SbfS3SbdVAInv;VCST;VXGL;A5").
Variable bd0 : list bitem.
Variable Q : assn.

Hypothesis TGT_bodyN : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S53R2A1S89S3Vok;S2bS3VJAFv;S53S90A2S39R3R2A5VQ;A4F_;Ftp;Frho2;").
Hypothesis TGT_after0 : ltac2:(tb__ "0|1|
S10S4S30Q40A1A1S53R2A1S1S0S2eS33R3S15P191A1A2Z0M0A3S0S2eS33R3S15P19aA1A2G0A3A2S89S3Vok;S2bS3VJAFv;S53S90A2Sa8R4R3A5VQ;A4F_;F_;Ftp;Frho2;").
Hypothesis TGT_bodyE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S89S3Vok;S2bS3VJAv;S91A1SaaR3R2A5VQ;A4F_;Ftp;Frho2;").
Hypothesis TGT_afterE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S89S3Vok;S2bS3VJAv;S91A1Sa9R3R2A5VQ;A4F_;Ftp;Frho2;").
Hypothesis Hb1 : ltac2:(tb__ "0|0|
S0S5S35S11S27S77A1A1Vbd0;A2S6A3"). Hypothesis Hl1 : ltac2:(tb__ "0|0|
S0S5S70S13S27S77A1A1S5aVbd0;A3S6A3").
Hypothesis Hb2 : ltac2:(tb__ "0|0|
S0S5S35S11S27S76A1A1Vbd0;A2S6A3"). Hypothesis Hl2 : ltac2:(tb__ "0|0|
S0S5S70S13S27S76A1A1S59Vbd0;A3S6A3").
Hypothesis Hb3 : ltac2:(tb__ "0|0|
S0S5S35S11S27S75A1A1Vbd0;A2S6A3"). Hypothesis Hl3 : ltac2:(tb__ "0|0|
S0S5S70S13S27S75A1A1SacVbd0;A3S6A3").
Hypothesis Hb4 : ltac2:(tb__ "0|0|
S0S5S35S11S27S74A1A1Vbd0;A2S6A3"). Hypothesis Hl4 : ltac2:(tb__ "0|0|
S0S5S70S13S27S74A1A1SabVbd0;A3S6A3").
Hypothesis Hbr : ltac2:(tb__ "0|0|
S0S5S35S11S27S72A1A1S8S34Vbd0;S55A3A2S6A3").

Lemma bd_below_run : ltac2:(tb__ "0|0|
S28S0S5Sc2S11S27S72A1A1S11S27R1A1A1A2S6A3S0S5S35S11S27R2A1A1S8S34Vbd0;S55A3A2S6A3F_;FT;").
Proof.
  intros T Hle. apply forallb_forall. intros it Hit. apply (proj1 (forallb_forall _ _) Hbr) in Hit.
  apply forallb_forall. intros ca Hca. eapply sv_below_mono; [apply Pos.leb_le; exact Hle | exact (proj1 (forallb_forall _ _) Hit ca Hca)].
Qed.

Lemma run1_sound : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S58R2A1S89S3Vok;S2bS3VJAv;S5dS56S52S8S34Vbd0;S55A3S5eA4A1S7bR3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (C1 & _ & _ & _ & Cn1 & _ & CV1 & _ & Ct1 & Cf1 & _ & _ & Ce1 & _).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 ok _ T_blr1 rho tp Q HP).
  apply (cfg_soundA segs FUEL_lo cps_land (ss_next (ax_S T_blr1)) [T_blr1] [XR_body1; XR_after1] (JAFv PhiP1 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) ok Q tp).
  - exact (ok_frameA_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 ok _ Hok).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP1 PhiP1_reads); [apply Pos.leb_le; exact Cn1 | | exact CV1].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct1, Cf1, (bd_below_run T_blr1 Ce1). reflexivity.
  - exact C1.
  - intros E rhoE [<-|[<-|[]]]; (eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRs_pureP segs ok _ (tblL (rho_sub rhoE s_landB))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')). }
      intros HT. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyN (rho_sub rhoE s_landB) tp HT)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')).
    + apply (TRs_pureP segs ok _ (tblL (rho_sub rhoE s_landA))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')). }
      intros HT. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_after0 (rho_sub rhoE s_landA) tp HT (land_after0_cnt rhoE))].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')).
  - left. reflexivity.
Qed.

Lemma run0_sound : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S57R2A1S89S3Vok;S2bS3VJAv;S5dS56S52S8S34Vbd0;S55A3S5eA4A1S7aR3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (_ & C0 & _ & _ & _ & Cn0 & _ & CV0 & _ & _ & Ct0 & Cf0 & _ & Ce0).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 ok _ T_blr0 rho tp Q HP).
  apply (cfg_soundA segs FUEL_lo cps_land (ss_next (ax_S T_blr0)) [T_blr0] [XR_body0; XR_after0] (JAFv PhiP0 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) ok Q tp).
  - exact (ok_frameA_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 ok _ Hok).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP0 PhiP0_reads); [apply Pos.leb_le; exact Cn0 | | exact CV0].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct0, Cf0, (bd_below_run T_blr0 Ce0). reflexivity.
  - exact C0.
  - intros E rhoE [<-|[<-|[]]]; (eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRs_pureP segs ok _ (ldef (rho_sub rhoE s_landBE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefBE rhoE HPe). }
      intros HLd. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyE (rho_sub rhoE s_landBE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_bodyE bd0 rhoE tp w Hb3 Hl3 Hw').
    + apply (TRs_pureP segs ok _ (ldef (rho_sub rhoE s_landAE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefAE rhoE HPe). }
      intros HLd. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_afterE (rho_sub rhoE s_landAE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_afterE bd0 rhoE tp w Hb4 Hl4 Hw').
  - left. reflexivity.
Qed.

Theorem blr_land_sound : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S0S5S35S11S27S72A1M0A1R3A2S6A3Sb9S8dVrho0;VP0;S13G0A1S16Z0M1A1G1R4S8S34SadS8S34Vbd0;S55A3A3A8S89S3Vok;S2bS3VJAv;S5dS73S52R5S5eA4A1S79R4R3A5VQ;A4F_;F_;Ftp;Frho;Fbd;").
Proof.
  intros bd rho tp Hbd HPAY.
  apply (X_E_blr (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun FBc FFc BXc rho1 tp1 HB => BLRP.build_line_index_rom_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ok Hok AC tp1)
           (bd0 ++ ENDOW) Q run1_sound run0_sound bd rho tp Hbd Hbr HPAY).
Qed.
End Pack.

Section PackX.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc0S3SbdVAInv;VCST;VXGL;A5").
Variable bd0 : list bitem.
Variable Q : world -> Prop.
Hypothesis TGT_bodyN : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S53R2A1S88S3S2bS3VJAFv;S53S90A2S39R3R2A5VQ;A3F_;Ftp;Frho2;").
Hypothesis TGT_after0 : ltac2:(tb__ "0|1|
S10S4S30Q40A1A1S53R2A1S1S0S2eS33R3S15P191A1A2Z0M0A3S0S2eS33R3S15P19aA1A2G0A3A2S88S3S2bS3VJAFv;S53S90A2Sa8R4R3A5VQ;A3F_;F_;Ftp;Frho2;").
Hypothesis TGT_bodyE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S88S3S2bS3VJAv;S91A1SaaR3R2A5VQ;A3F_;Ftp;Frho2;").
Hypothesis TGT_afterE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S88S3S2bS3VJAv;S91A1Sa9R3R2A5VQ;A3F_;Ftp;Frho2;").
Hypothesis Hb1 : ltac2:(tb__ "0|0|
S0S5S35S11S27S77A1A1Vbd0;A2S6A3"). Hypothesis Hl1 : ltac2:(tb__ "0|0|
S0S5S70S13S27S77A1A1S5aVbd0;A3S6A3").
Hypothesis Hb2 : ltac2:(tb__ "0|0|
S0S5S35S11S27S76A1A1Vbd0;A2S6A3"). Hypothesis Hl2 : ltac2:(tb__ "0|0|
S0S5S70S13S27S76A1A1S59Vbd0;A3S6A3").
Hypothesis Hb3 : ltac2:(tb__ "0|0|
S0S5S35S11S27S75A1A1Vbd0;A2S6A3"). Hypothesis Hl3 : ltac2:(tb__ "0|0|
S0S5S70S13S27S75A1A1SacVbd0;A3S6A3").
Hypothesis Hb4 : ltac2:(tb__ "0|0|
S0S5S35S11S27S74A1A1Vbd0;A2S6A3"). Hypothesis Hl4 : ltac2:(tb__ "0|0|
S0S5S70S13S27S74A1A1SabVbd0;A3S6A3").
Hypothesis Hbr : ltac2:(tb__ "0|0|
S0S5S35S11S27S72A1A1S8S34Vbd0;S55A3A2S6A3").

Lemma bd_below_runX : ltac2:(tb__ "0|0|
S28S0S5Sc2S11S27S72A1A1S11S27R1A1A1A2S6A3S0S5S35S11S27R2A1A1S8S34Vbd0;S55A3A2S6A3F_;FT;").
Proof.
  intros T Hle. apply forallb_forall. intros it Hit. apply (proj1 (forallb_forall _ _) Hbr) in Hit.
  apply forallb_forall. intros ca Hca. eapply sv_below_mono; [apply Pos.leb_le; exact Hle | exact (proj1 (forallb_forall _ _) Hit ca Hca)].
Qed.

Lemma run1_complete : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S58R2A1S88S3S2bS3VJAv;S5dS56S52S8S34Vbd0;S55A3S5eA4A1S7bR3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (_ & _ & C1 & _ & Cn1 & _ & CV1 & _ & Ct1 & Cf1 & _ & _ & Ce1 & _).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ T_blr1 rho tp Q HP).
  apply (cfg_complete_autoA segs FUEL_lo cps_land (ss_next (ax_S T_blr1)) [mkVNA T_blr1 601 z0] [mkVNA XR_body1 600 z0; mkVNA XR_after1 600 z0]
           (JAFv PhiP1 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) Q tp) with (n := mkVNA T_blr1 601 z0).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP1 PhiP1_reads); [apply Pos.leb_le; exact Cn1 | | exact CV1].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct1, Cf1, (bd_below_runX T_blr1 Ce1). reflexivity.
  - intros n [<-|[]]. cbn [vna_state]. apply Pos.le_refl.
  - exact C1.
  - intros E rhoE [<-|[<-|[]]]; cbn [vna_state]; (eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRe_pureP segs _ (tblL (rho_sub rhoE s_landB))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')). }
      intros HT. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyN (rho_sub rhoE s_landB) tp HT)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')).
    + apply (TRe_pureP segs _ (tblL (rho_sub rhoE s_landA))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')). }
      intros HT. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_after0 (rho_sub rhoE s_landA) tp HT (land_after0_cnt rhoE))].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')).
  - left. reflexivity.
Qed.

Lemma run0_complete : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S57R2A1S88S3S2bS3VJAv;S5dS56S52S8S34Vbd0;S55A3S5eA4A1S7aR3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (_ & _ & _ & C0 & _ & Cn0 & _ & CV0 & _ & _ & Ct0 & Cf0 & _ & Ce0).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ T_blr0 rho tp Q HP).
  apply (cfg_complete_autoA segs FUEL_lo cps_land (ss_next (ax_S T_blr0)) [mkVNA T_blr0 601 z0] [mkVNA XR_body0 600 z0; mkVNA XR_after0 600 z0]
           (JAFv PhiP0 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) Q tp) with (n := mkVNA T_blr0 601 z0).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP0 PhiP0_reads); [apply Pos.leb_le; exact Cn0 | | exact CV0].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct0, Cf0, (bd_below_runX T_blr0 Ce0). reflexivity.
  - intros n [<-|[]]. cbn [vna_state]. apply Pos.le_refl.
  - exact C0.
  - intros E rhoE [<-|[<-|[]]]; cbn [vna_state]; (eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRe_pureP segs _ (ldef (rho_sub rhoE s_landBE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefBE rhoE HPe). }
      intros HLd. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyE (rho_sub rhoE s_landBE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_bodyE bd0 rhoE tp w Hb3 Hl3 Hw').
    + apply (TRe_pureP segs _ (ldef (rho_sub rhoE s_landAE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefAE rhoE HPe). }
      intros HLd. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_afterE (rho_sub rhoE s_landAE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_afterE bd0 rhoE tp w Hb4 Hl4 Hw').
  - left. reflexivity.
Qed.

Theorem blr_land_complete : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S0S5S35S11S27S72A1M0A1R3A2S6A3Sb9S8dVrho0;VP0;S13G0A1S16Z0M1A1G1R4S8S34SadS8S34Vbd0;S55A3A3A8S88S3S2bS3VJAv;S5dS73S52R5S5eA4A1S79R4R3A5VQ;A3F_;F_;Ftp;Frho;Fbd;").
Proof.
  intros bd rho tp Hbd HPAY.
  apply (X_E_blr (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun FBc FFc BXc rho1 tp1 HB => BLRP.build_line_index_rom_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ACX tp1)
           (bd0 ++ ENDOW) Q run1_complete run0_complete bd rho tp Hbd Hbr HPAY).
Qed.
End PackX.

End Sum.

Print Assumptions blr_land_sound.
Print Assumptions blr_land_complete.
