(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "true"; "bool"; "app"; "cons"; "nil"; "Some"; "fst"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "TPA"; "frinA"; "tvinA"; "ANone"; "JA"; "amode"; "fbinA"; "ffinA"; "nd_am"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "holds"; "SLit"; "ss_facts"; "sprop_eqb"; "ss_next"; "SPUlt"; "sobj"; "SPUle"; "sprop_below"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "BXok_d"; "bxt"; "bd_wpos"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "PhisS"; "ldefR"; "vNV"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF_pf.VRNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF_eqs"; "cutsCF"; "exitsCF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "nd_succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "L_cf0"; "K_rp"; "nd_rp"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF"; "vcf"; "kept_vr"; "nd_cf"; "PDk_vr"; "vI"; "vcfB"; "E_c0"; "L_x"; "R_c"; "bnd_nt"; "nd_fail"; "E_c"; "Nt"; "PD_vr"; "Wt"; "Xk_vr"; "brest_vr"; "cbI"; "cntI"; "nv_pos"; "nv_src"; "passed_vr"; "room_vr"; "s_c"; "slot_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF_chk"; "len_src"; "slot_src"; "Fx"; "rp_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF.VRN"; "Pre_vr"; "nd0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pdescA"; "robjs_okF"; "xrs_okF"; "FFx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD_eqs Lib_load_obj_epiS1 Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_epiCF Lib_load_obj_epiCF_eqs Lib_load_obj_epiCF_chk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module VRNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf. End VRNP.

Lemma efmeas_z0 : ltac2:(tb__ "0|1|
SeS12S3SdS1fS2cSdS37S0S1S1SeS12A2M0S3A2S1SdS20A2S0G0S3S0SeS12R5R4A4R3A4S0SdS20R2S7aA4A4R1A2S34R2S36Z2Z40A2A2A3Frho;Fr;Fk;Fnd;FT;").
Proof. intros. unfold efmeasA. cbn [ef_rank ef_var fst snd]. unfold z0. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.
Lemma efmeas_lit : ltac2:(tb__ "0|2|
SeS12S3SdSdS1fS2dS32Z0R2A2S33R2S36Z2Z40A2M0A2A2S2cSdS37S0S1S1SeS12A2M1S3A2S1SdS20A2S0G1S3S0SeS12R7R6A4R5A4S0SdS20R4S23R3A1A4A4R2A2S35S34R4G0A2R3A2A3F_;Frho;Fc;Fr;Fk;Fnd;FT;").
Proof. intros T nd k r c rho Hc. unfold efmeasA. cbn [ef_rank ef_var fst snd]. change (bv_unsigned (eval rho (SLit c))) with (uval rho (SLit c)). rewrite uval_lit by lia. lia. Qed.
Lemma efmeas_vcf : ltac2:(tb__ "0|2|
SeS12S3SdSdS1fS2cSdS37S0S1S1SeS12A2M0S3A2S1SdS20A2S0G0S3S0SeS12R6R5A4R4A4S0SdS20R3S5dR2A1M1A4A4R1A2S35S34R3S36Z2Z40A2A2S3fR1G1A2A2A3Frho;Fc;Fr;Fk;Fnd;FT;").
Proof. reflexivity. Qed.

Lemma vcf_val : ltac2:(tb__ "0|0|
S1fSdS2dS32Z0R1A2S32R1Z1fA2A2S2cSdS3fR3S5dR2A1A2S35S3fR3S62A2R2A2A3F_;Fc;Frho;").
Proof.
  intros rho c Hc. unfold vcf.
  assert (E4 : uval rho (SLit 32) = 32) by (apply uval_lit; lia).
  assert (Ec : uval rho (SLit c) = c) by (apply uval_lit; lia).
  assert (HM : uval rho vcfB <= 18446744073709551584).
  { unfold vcfB, uval. rewrite U_mul. fold (uval rho (SLit 32)). rewrite E4. unfold M64v.
    change 18446744073709551616 with (32 * 576460752303423488). rewrite Z.mul_mod_distr_l by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned (eval rho (SAlu ALU_SUB vNV vI))) 576460752303423488 ltac:(lia)). lia. }
  rewrite uval_add_small by (rewrite Ec; lia). rewrite Ec. reflexivity.
Qed.

Lemma meas_vcf_12 : ltac2:(tb__ "0|2|
S1fS1fS2cSdS3fR1S62A2S3fR2S62A2A3S2dS32Z0S35S34Z189S36Z2Z40A2A2M0S3fR2S5dZ1dA1A2A2M1A2S33G1S35G0S3fR3S5dZ1eA1A2A2A2A2F_;Frho';Frho;").
Proof.
  intros rho rho' EV. rewrite !vcf_val by lia. rewrite EV. pose proof (uval_range rho vcfB) as RV. lia.
Qed.

Lemma nv_pos_of_src : ltac2:(tb__ "0|0|
S1fS22R1S71A2S22R2S70A2F_;Frho;").
Proof.
  intros rho H. unfold nv_src in H. apply (proj1 (holds_bgeu _ _ _)) in H.
  change (bv_unsigned (eval rho (SLit 3))) with (uval rho (SLit 3)) in H. rewrite uval_lit in H by lia.
  change (bv_unsigned (eval rho (SMd M_MUL vNV (SLit 3)))) with (uval rho (SMd M_MUL vNV (SLit 3))) in H.
  unfold nv_pos. apply (proj2 (h_ult _ _ _)). rewrite uval_lit by lia. pose proof (uval_range rho vNV) as R.
  destruct (Z.eq_dec (uval rho vNV) 0) as [E|N]; [|lia].
  exfalso. rewrite uval_mul_small in H by (rewrite E; lia). rewrite E in H. lia.
Qed.

Lemma cf_vals : ltac2:(tb__ "0|4|
S1fS2S21A1S47S21S22R2A1R1A3S2cS5S4eS21S25S27S61S46A2A1R2A3S4A3S2cS5S7bR3A1S4A3S2dS33S3fR5S61A2M0S3fR5S46A2M1A2S2dS32G1Z4000001A2S2dS2cSdS3fR5S6fA2S34Z3M2G0A2M3A3S2dS2cSdS3fR5S6bA2S35G3G2A2A3S2dS2cSdS3fR5S69A2S35S34G2G1A2Z2A2A3S2cSdS3fR5S6eA2S34ZcG0A2A3A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HI HL. unfold len_src in HL. apply andb_prop in HL as [HL H3]. apply andb_prop in HL as [H1 H2].
  pose proof (holds_mem _ _ _ HF HI) as FI. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  unfold fact_nv in F1. rewrite h_ult in FI. rewrite h_ule in F1, F2, F3. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho vI) as RI. pose proof (uval_range rho vNV) as RN. pose proof (uval_range rho pNX) as RX. pose proof (uval_range rho vLEN) as RL.
  rewrite uval_add_small in F2 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F2 by lia.
  assert (Ec : uval rho cntI = 3 * uval rho vI) by (unfold cntI; apply uval_mul_lit; lia).
  assert (EW : uval rho Wt = 3 * uval rho vI + 3) by (unfold Wt; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (E3N : uval rho (SMd M_MUL (SLit 3) vNV) = 3 * uval rho vNV) by (apply uval_mul_lit; lia).
  assert (EN : uval rho Nt = 3 * uval rho vNV + 2) by (unfold Nt; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (Eb : uval rho cbI = 12 * uval rho vI) by (unfold cbI; rewrite uval_mul_comm; rewrite uval_mul_lit by lia; lia).
  repeat split; lia.
Qed.
Lemma room_holds : ltac2:(tb__ "0|0|
S1fS2S21A1S47S21S22R2A1R1A3S2cS5S4eS21S25S27S61S46A2A1R2A3S4A3S2cS5S7bR3A1S4A3S47S21S22R5A1S73A3F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HI HL. destruct (cf_vals rho F HF HI HL) as (V1 & V2 & V3 & V4 & V5 & V6).
  assert (E4W : uval rho (SMd M_MUL (SLit 4) Wt) = 4 * uval rho Wt) by (apply uval_mul_lit; lia).
  assert (E4N : uval rho (SMd M_MUL (SLit 4) Nt) = 4 * uval rho Nt) by (apply uval_mul_lit; lia).
  unfold room_vr. constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - lia.
  - unfold VRN.B_EW. rewrite uval_lit by lia. lia.
  - lia.
Qed.
Lemma slot_holds : ltac2:(tb__ "0|0|
S1fS2S21A1S20S47S21S22R3A1R2A3S2cS5S7cR2R3A2S4A3S47S21S22R5A1S75R3A1A3F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H. unfold slot_src in H. apply andb_prop in H as [H HL]. apply andb_prop in H as [H HI]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (cf_vals rho F HF HI HL) as (V1 & V2 & V3 & V4 & V5 & V6).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F1, F2, F3. rewrite uval_lit in F2, F3 by lia. pose proof (uval_range rho k) as RK.
  assert (E4k : uval rho (kb 4 k) = 4 * uval rho k) by (unfold kb; apply uval_mul_lit; lia).
  unfold slot_facts. constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - lia.
  - unfold VRN.B32. rewrite uval_lit by lia. lia.
Qed.

Lemma slot_kpos : ltac2:(tb__ "0|1|
S1fS2S21A1S20S47S21S22R3A1R2A3S2cS5S7cR2R3A2S4A3S2dS32Z3S3fR5R3A2M0A2S32G0ZffffffffA2A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H. unfold slot_src in H. apply andb_prop in H as [H HL]. apply andb_prop in H as [H HI]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (cf_vals rho F HF HI HL) as (V1 & V2 & V3 & V4 & V5 & V6).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. rewrite h_ule in F1, F2. rewrite uval_lit in F2 by lia.
  pose proof (uval_range rho vI) as RI. lia.
Qed.

Lemma szL_val : ltac2:(tb__ "0|0|
S1fS2S21A1S47S21S22R2A1R1A3S2cS5S4eS21S25S29S96S23ZffffffffA1A2A1R2A3S4A3S2cSdS3fR4Sa4A2S34Z10S3fR4S96A2A2A3F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF C. pose proof (holds_mem _ _ _ HF C) as H. rewrite h_ule, uval_lit in H by lia.
  pose proof (uval_range rho xLK) as R. unfold szL, kb. apply uval_mul_lit; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S86S1fS2S2bQ40A1A1S5aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S9fS11VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SdS95VCST;R1A2S2dS32Z0R2A2S33R2S9bA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SdS95VXGL;R1A2S2dS32Z0R2A2S33R2S9bA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SdSa0R1A1S95VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1SdSdA2SdA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S1fOFr;") := ltac2:(tb__ "0|0|
Sa5VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S19VAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S13Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3bVAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S13VPhi;Vnd;Ad").

Lemma h0_ltNF : (h0 < NF)%positive. Proof. reflexivity. Qed.
Lemma HamC_vr : nd_am VRN.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vr : ltac2:(tb__ "0|0|
S47S97S97S2cS1aS1dScSeS12R1A3A1S18A3Ld;S6aA3"). Proof. repeat constructor. Qed.
Lemma P0_vr_mono : ltac2:(tb__ "0|2|
S2S1SdSdA2M0A1M1G1S2S1G0SdA2A1S1fG0S4dG0R1R5A3S4dG0R2R5A3F_;Fbn;S52R5R3R2A3S52R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.

Lemma lo_robjsF0 : ltac2:(tb__ "0|0|
S86S1fS2S21A1S2S1S20S20A2A1S2S28A1S1fS2S2bQ40A1A1S5aVAInv;R8R3R2R1A4S47S21S22R8A1R7A3VP0;Vrho0;A1S7fS53Vrho0;RaA3S15Vrho0;RcA2S8fRcS88S87RdA1A1A2S17VFB;ReRdRbA4S90ReRcA2S91RfRdA2S16VFF;R11R10S50A4S2cS5Sa1R10RfS50S51ReA5S4A3S98VCST;Vrho0;VFB;VFF;R12R10S50RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
Qed.
Lemma lo_xrsF0 : ltac2:(tb__ "0|1|
S86S1fS2S21A1S2S1S20S20A2A1M0G0S1fS2S2bQ40A1A1S5aVAInv;R8R3R2R1A4S47S21S22R8A1R7A3VP0;Vrho0;A1S7fS53Vrho0;RaA3S15Vrho0;RcA2S8fRcS88S87RdA1A1A2S17VFB;ReRdRbA4S90ReRcA2S91RfRdA2S16VFF;R11R10S50A4S2cS5Sa3R10RfS50Sa2ReA5S4A3S99VCST;VXGL;Vrho0;VFB;VFF;R12R10S50RfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tv frL xextraLO X rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
  intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho tv frL r a Hav HP0 HE Ha).
Qed.
Lemma payA_same : ltac2:(tb__ "0|1|
S2S21A1S2S43A1S2cS5S42R1A1S4A3SadS53Vrho0;VP0;R3S23Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Lemma HIN_c : ltac2:(tb__ "0|1|
S1fS79S86S1fS2S2bQ40A1A1S5aS47S21S22R6A1S24SfS68A1A1A3VP0;Vrho0;A1S7fS53Vrho0;R8A3VAInv;R7R6R5R4A4S15Vrho0;R8A2S8fRbS88S87R9A1A1A2S1bVFB;RaA2S1cVFF;RbA2S17VFB;RcReS6S1S20S20A2S5eS72A3M0A4S90RfG0A2S91R10G0A2S16VFF;RfR11S50A4S2dS98VCST;Vrho0;VFB;VFF;R12S5eS50S65A8S2dS99VCST;VXGL;Vrho0;VFB;VFF;R12S5eS50S6cA9S52S92VFB;R12S5eA3S9aVFF;R12S50A3S77S76R12S65R11A3S74A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof epiCF_chk_site as (CR & CX & _ & _ & FkB & FvF & _ & _ & _ & _ & _ & _ & W17 & W15 & W12 & W14).
  assert (HNk : tvinA FB Ai rho kept_vr) by (apply (tvinA_sublist FB Ai rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vr) by (exact (tvd_app_l rho kept_vr passed_vr HD)).
  assert (HZk : tvz rho kept_vr) by (apply (tvz_sublist rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF0 Ai rho _ kept_vr R_c rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF0 Ai rho _ kept_vr Xk_vr rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold VRNP.P0_vr. rewrite !rw_call'. rewrite W17, W15, W12, W14.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    pose proof (holds_mem _ _ _ HF FvF) as HvF. rewrite h_ule, uval_lit in HvF by lia.
    pose proof (holds_mem _ _ _ HF FkB) as HkB. rewrite h_ule, uval_lit in HkB by lia.
    assert (E824 : uval rho (SAlu ALU_ADD vF (SLit 728)) = uval rho vF + 728) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [|split].
    + intros Hk. apply (tvz_in_kd rho (kept_vr ++ passed_vr) d_ac 4 k_ac HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32, Lib_vec_reserve.B32; lia | exact Hk].
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite E824. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SdS2S2bQ40A1A1S49F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S30SeS1fS2S2bQ40A1A1S49S47S21S22R3A1S24SfR4A1A1A3VTR;S2fS11R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S49S49S49S4cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S49OS49S4cR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S30S30SeSeS78S2S28A1M0S2S1SeS82A2M1A1S2S1S20S20A2M2A1S49S1fS2S2bQ40A1A1M3G2S4dG2R1R5A3S4dG2R2S10RbA1A3F_;Fr;S2cSbG0A1S85RaR9R8A3S9G0R7A2A3S2cS5S84RbRaR9R8S48G1SeSaSeS82A2R7A4A5S4A3S1fG3VTR;S2fS11RfRdR2R1A5S81S11S26SfRdA1A1R2R1RaA5A2Ftp1;Frho1;S2S5bA1M4S79S5aS31S11R9R8R10S0G4S89R3S8aR2R1A2A4A5R13RaR9R4R2A4R13S77S76RbRfS5cR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SeS82G4S79S5aS1fG3G4S79S5aS4dG1S0SeS82RaR9A4R14A3S31S11R12R11R19S0G4S89R9S8aR8R7A2A4A5R1cR13R12RaR8A4S7fS26SfR1aA1A1S77S76R14R18S5cR9R13RaA3A3R19A2R8A3S31S11R9R8ReS0G4S89R7S8aR6R5A2A4A5ReS77S76R16R1aS5cRbR15RcA3A3R1bA2R15RaR9R8R6A6S2dSabR17S5cRcR16RdA3R1bR1cR1dR10R1eR19RbA9S1fS80R18S5cRdR17ReA3R1cR1dSfR1eA1SfR1fA1SfR11A1R1RcA9VTR;S2fS11S83R11S77S76R19R1dS5cReR18RfA3A3R1eA2R18RdRcA5SacR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2fS11R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S1fOF_;S12SeS1fS2S2bQ40A1A1S49R6R3A1VTR;S2fS11VJAv;R6A1R5R4R3A5R2A2F_;VTR;S2fS11VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CVRN : ltac2:(tb__ "0|1|
S2S1SdSdA2M0A1S2S1G0SdA2A1S41S1fS2S2bQ40A1A1S40Z3R3A2VTR;S2fS11S14VAInv;VCST;VXGL;VKc;S52R6R5A2R6R5R4S13S93S8bS4S8dA3AaS8cR3R2A5S81S11S8eR3R2S94VAInv;VCST;VXGL;VKc;S52S13S60R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CUTC : ltac2:(tb__ "0|5|
SeS12S3S1SdS20A2M0S1fS2S2bQ40A1A1M1SdG1S4dS1S1S1SeS12A2M2S3A2M3G0A2S0G3G0S0G2S3S0SeS12R8R7A4R6A4R5A4S54A3S38S44R7R5A3S2dS32Z0S37S0G3G0S0G2S3S0SeS12RaR9A4R8A4R7A4R6A2M4A2S33G4R4A2A2VTR;S2fS11VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CONT_RP : ltac2:(tb__ "0|3|
S1fS2S2bQ40A1A1M0SdG0S45R4A1S2dS32Z0S37S0S1S1SeS12A2M1S3A2S1SdS20A2S0G1S3S0SeS12S58S59A4U0A4S0SdS20Z187S23Z37fA1A4A4R5A2M2A2S33G2R3A2A2VTR;S2fS11VJAv;S59A1S58R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;").

Lemma X_E_c0 : ltac2:(tb__ "0|3|
S1fS2S2bQ40A1A1M0G0VTR;S2fS11VJAFv;S38S44U0M1A2S5fA2S63R3R2A5VFAM;S37S0S1S1SeS12A2M2S3A2S1SdS20A2S0G2S3S0SeS12S63S5fA4G1A4S0SdS20Z189S5dZ1eA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiCF_checks_vr as (Cxf & CEc & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & Cnb & Cbr & Cnp & Cwp).
  pose proof epiCF_chk_site as (CR & CX & FI & FL & FkB & FvF & F16 & FLK & FLD & FLDK & F30 & CVb & _).

  apply (TR_pre (SPA segs (JAv nd_cf) E_c rho tp)).
  { intros w Hw. rewrite <- CEc. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - exact (SPA_axforms segs (JAv nd_cf) (xf_vr E_c0) rho E_c0 E_c1 tp w Cxf Hw).
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. exact (room_holds rho _ HF1 FI FL). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv nd_cf] in HZ. intros E0.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [unfold tv_vr; apply in_or_app; left; exact lines_in_kept_vr|].
    unfold tnz. cbn [fst]. intros H. exact (H E0). }
  intros Hnull.
  unfold nd_cf, tv_vr.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX VRNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VRN.Pre_vr (ndh h0 true VRN.nd0) PDk_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRN eq_refl
           E_c s_c R_c Xk_vr rho tp kept_vr passed_vr frL bd_vr brest_vr (AHead pH true) (FAM (efmeasA (E_c0, nd_cf, 0%nat, (393, vcf 30)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. exact (payA_same _ bd_vr Cwp).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_c rho ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.

    assert (HPHI' : ldefR rho').
    { apply (ldefR_keep rho rho'); [| | exact HPHI].
      - intros v Hv. apply (proj1 Hag). cbn [V_ldR In] in Hv. destruct Hv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
      - intros z Hz.
        pose proof (szL_val rho _ HF FLK) as ESZ.
        destruct (Z.eq_dec (uval rho xLD) 0) as [E0|Hnz]; [pose proof (Hnull E0); lia|].
        pose proof (holds_mem _ _ _ HF FLD) as H3. rewrite h_ule, uval_lit in H3 by lia.
        pose proof (holds_mem _ _ _ HF F16) as H1. rewrite h_ule, uval_lit in H1 by lia. fold szL in H1.
        pose proof (holds_mem _ _ _ HF FLDK) as H4. rewrite h_ule in H4. fold szL in H4.
        pose proof (holds_mem _ _ _ HF F30) as H6. rewrite h_ule, uval_lit in H6 by lia.
        rewrite (uval_add_small rho xLD szL) in H4 by lia.
        exact (keptK_lines CST FB FF rho0 rho kept_vr frL rho' HK lines_in_kept_vr Hnz ltac:(lia) ltac:(unfold B32, Lib_vec_reserve.B32; lia) z Hz). }

    assert (EV : uval rho' vcfB = uval rho vcfB).
    { unfold uval. rewrite <- (eval_agree_vals (ss_next (ax_S E_c)) rho rho' vcfB Hag eq_refl). reflexivity. }
    pose proof epiCF_checks_vr_nd as (Nk & Ng & Nf & Tk0 & Tg0 & Tf0 & Bk & Bg & Bf & Tik & Tig & Tif & Sk & Sg & Fbk & Fbg & _ & _ & _ & _ & _).
    pose proof epiCF_chk_cont as (Ssk & Ssg & Cgk & CidV & Csub).
    cbn [PDk_vr liftPD PDh PD_vr map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite Tk0, Nk.
      apply (TR_pre (SPA segs (JAv nd_cf) K_w rho' tp')).
      { intros w Hw. unfold K_w. rewrite <- Sk. apply (SPA_refacts_JA segs); [| exact Fbk |].
        - rewrite <- Tik. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_cf) (xfb_vr T_keep0) rho' T_keep0 B_keep tp' w Bk Hw).
        - intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. unfold inj_keep. apply Forall_app. split; [exact (slot_holds rho' _ k_ac HF2 Ssk)|].
          constructor; [|constructor].
          pose proof (slot_kpos rho' _ k_ac HF2 Ssk) as KP.
          assert (TNZ : tnz rho' (d_ac, kb 4 k_ac)).
          { unfold tnz. cbn [fst]. pose proof HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (_ & _ & HZ') & _). cbn [nd_tv nd_cf] in HZ'.
            apply (tvz_in_kd rho' tv_vr d_ac 4 k_ac HZ'); [exact acol_in_tv_vr | lia | unfold B32, Lib_vec_reserve.B32; lia | lia]. }
          pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue ALA nd_cf rho' tp' tr md (d_ac, kb 4 k_ac) eq_refl HJ
                        acol_in_tv_vr TNZ) as TF.
          apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity. }
      apply (CUTC K_w nd_cf 0%nat (393, vcf 29) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      rewrite !efmeas_vcf. exact (meas_vcf_12 rho rho' EV).
    +
      rewrite Tf0, Nf.
      apply (TR_pre (SPA segs (JAv nd_fail) T_fail rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fail) (xfb_vr T_fail0) rho' T_fail0 B_fail tp' w Bf Hw). }
      apply (CUTC T_fail nd_fail 0%nat (392, SLit 10) rho' tp'); [do 4 right; left; reflexivity | exact HPHI' |].
      rewrite efmeas_vcf, efmeas_lit by lia. pose proof (uval_range rho (vcf 30)) as RV. lia.
    +
      rewrite Tg0, Ng.
      apply ent_chkS_unf in Cgk as (Ce & Cid & Cnp' & Cnb' & Ctv & Cfr & Cbd & Cam').
      apply (TR_pre (SPA segs (JAv nd_cf) K_w (rho_sub rho' s_gk) tp')).
      { intros w Hw.
        assert (HwS : SPA segs (JAv nd_grown) T_grownS rho' tp' w).
        { rewrite <- Sg. apply (SPA_refacts_JA segs); [| exact Fbg |].
          - rewrite <- Tig. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_grown) (xfb_vr T_grown0) rho' T_grown0 B_grown tp' w Bg Hw).
          - intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. unfold inj_grown. exact (slot_holds rho' _ vKg HF2 Ssg). }
        exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc T_grownS K_w s_gk nd_grown nd_cf rho' tp' w Ce Cid Cnp' Cnb' Ctv Cfr Cbd Cam' HwS). }
      apply (CUTC K_w nd_cf 0%nat (393, vcf 29) (rho_sub rho' s_gk) tp'); [right; left; reflexivity | exact (phi_sub V_ldR ldefR ldefR_reads s_gk rho' CidV HPHI') |].
      rewrite !efmeas_vcf. unfold uval at 1. rewrite <- (eval_subst rho' s_gk (vcf 29)), Csub. fold (uval rho' (vcf 29)).
      exact (meas_vcf_12 rho rho' EV).
Qed.

Lemma bnd_holds : ltac2:(tb__ "0|0|
S1fS2S21A1S45R2A1S47S21S22R3A1R2A3S2cS5S7bR3A1S4A3S47S21S22R5A1S7S21S66S8S21A1A3A3F_;F_;F_;FF;Frho;").
Proof using .
  intros rho F HPHI HF1 FL. constructor; [|constructor].
  unfold len_src in FL. apply andb_prop in FL as [FL F3]. apply andb_prop in FL as [_ F2].
  exact (proj2 (rate2_bounds rho (ldefR_rate rho HPHI) (holds_mem _ _ _ HF1 F2) (holds_mem _ _ _ HF1 F3))).
Qed.

Lemma X_L_x : ltac2:(tb__ "0|3|
S1fS2S2bQ40A1A1M0G0VTR;S2fS11VJAFv;S38S44U0M1A2S5fA2S64R3R2A5VFAM;S37S0S1S1SeS12A2M2S3A2S1SdS20A2S0G2S3S0SeS12S64S5fA4G1A4S0SdS20Z188S23Z5A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiCF_checks_inj as (CxF & Cfb & _).
  pose proof epiCF_chk_exit as (FL & _ & _ & Cptv & Cpbd & Cx & _).
  unfold rp_chk in Cx. apply lazy_andb_prop in Cx as [Cx CidV].
  apply ent_chkS_unf in Cx as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_rp) K_rp (rho_sub rho s_x) tp)).
  { intros w Hw.
    assert (HwF : SPA segs (JAv (NDA tvL frL bd_xe (AHead pH true))) L_xF rho tp w).
    { rewrite <- CxF. apply (SPA_refacts_JA segs); [| exact Cfb |].
      - apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL bd_vr bd_xe (AHead pH true) L_x rho tp w Cpbd).
        exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vr tvL frL bd_vr (AHead pH true) L_x rho tp w Cptv Hw).
      - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. exact (bnd_holds rho _ HPHI HF1 FL). }
    exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_xF K_rp s_x (NDA tvL frL bd_xe (AHead pH true)) nd_rp rho tp w
             Ce Cid Cnp Cnb Ctv Cfr Cbd Cam HwF). }
  apply (CONT_RP (rho_sub rho s_x) tp); [exact (phi_sub V_ldR ldefR ldefR_reads s_x rho CidV HPHI) |].
  rewrite !efmeas_lit by lia. lia.
Qed.

Lemma X_Lf : ltac2:(tb__ "0|5|
SeSeS78S1fS2S2bQ40A1A1M0G0S2cSeSa8R6S6S21S7S21S66S8S21A1A3M1S24SfR6A1A1A3A2R5A3S2cS5S4fS21S2aS26SfR7A1M2A1A1S6S21G1S24G2A1A3A3S4A3S2cS5S7bS7dR8A1A1S4A3S2cS5S7eR8R7S6dA3S4A3VTR;S2fS11VJAFv;S38S44U0M3A2S67A2RaR7R6A5VFAM;S37S0S1S1SeS12A2M4S3A2S1SdS20A2S0G4S3S0SeS12RaS67A4G3A4S0SdS20Z188S23Z5A1A4A4R7A2R5A2A2F_;F_;F_;F_;Ftp0;Ftp;Frho;Fs;FLF;FL;").
Proof.
  intros L LF s rho tp tp0 CxF Cfb FL Cx. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiCF_chk_exit as (_ & _ & _ & Cptv & _).
  unfold rp_chk in Cx. apply lazy_andb_prop in Cx as [Cx CidV].
  apply ent_chkS_unf in Cx as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_rp) K_rp (rho_sub rho s) tp)).
  { intros w Hw.
    assert (HwF : SPA segs (JAv (NDA tvL frL brest_vr (AHead pH true))) LF rho tp w).
    { rewrite <- CxF. apply (SPA_refacts_JA segs); [| exact Cfb |].
      - exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vr tvL frL brest_vr (AHead pH true) L rho tp w Cptv Hw).
      - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. exact (bnd_holds rho _ HPHI HF1 FL). }
    exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc LF K_rp s (NDA tvL frL brest_vr (AHead pH true)) nd_rp rho tp w
             Ce Cid Cnp Cnb Ctv Cfr Cbd Cam HwF). }
  apply (CONT_RP (rho_sub rho s) tp); [exact (phi_sub V_ldR ldefR ldefR_reads s rho CidV HPHI) |].
  rewrite !efmeas_lit by lia. lia.
Qed.

Lemma exitsCF_ok : ltac2:(tb__ "0|4|
SeS12S3S1SdS20A2M0S1fS2S2bQ40A1A1M1G1S4dS1S1S1SeS12A2M2S3A2M3G0A2S0G3G0S0G2S3S0SeS12R7R6A4R5A4R4A4S55A3VTR;S2fS11VJAFv;S38S44R6A2R7A2R8R4R3A5VFAM;S37S0G3G0S0G2S3S0SeS12R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsCF In] in Hin.
  pose proof epiCF_chk_exit as (_ & FL0 & FL1 & _ & _ & _ & CL0 & CL1).
  pose proof epiCF_checks_inj as (_ & _ & E0 & B0 & E1 & B1).
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-.
  - apply X_E_c0.
  - apply X_L_x.
  - exact (X_Lf Lf0 Lf0F s_f0 rho tp tp0 E0 B0 FL0 CL0).
  - exact (X_Lf Lf1 Lf1F s_f1 rho tp tp0 E1 B1 FL1 CL1).
Qed.

Lemma X_L_cf0 : ltac2:(tb__ "0|3|
S1fS2S2bQ40A1A1M0G0VTR;S2fS11VJAFv;S38S44U0M1A2S56A2S57R3R2A5VFAM;S37S0S1S1SeS12A2M2S3A2S1SdS20A2S0G2S3S0SeS12S57S56A4G1A4S0SdS20Z18aS7aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiCF_checks_ent as (CE & Cfb & Fsrc & Fc0 & Zwf & Zsd & Znx & ZE & _).
  pose proof epiCF_chk_ent as (Nd & Cptv & Cpbd & Cx & CidV).
  apply ent_chkS_unf in Cx as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_cf) L_cfE rho tp)).
  { intros w Hw. rewrite Nd in Hw. rewrite <- CE. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - unfold nd_cf. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vr frL bd_cf bd_vr (AHead pH true) L_cf0 rho tp w Cpbd).
      exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL tv_vr frL bd_cf (AHead pH true) L_cf0 rho tp w Cptv Hw).
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1].
      constructor; [exact (ldefR_nv rho HPHI) | constructor; [exact (nv_pos_of_src rho (holds_mem _ _ _ HF1 Fsrc)) | constructor]]. }
  apply TR_facts. intros HFE.
  apply (TR_pre (SPA segs (JAv nd_cf) C_cf (rho_sub rho s_ent) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_cfZ C_cf s_ent nd_cf nd_cf rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    rewrite <- ZE. apply (SPA_restate segs (JAv nd_cf) rho L_cfE (ax_S L_cfZ) tp w _ _ Zwf Zsd Znx); [| constructor | exact Hw].
    constructor; [|constructor]. cbn [fst snd]. apply bv_eq. exact (proj1 (holds_nbne _ _ _) (holds_mem _ _ _ HFE Fc0)). }
  apply (CUTC C_cf nd_cf 0%nat (393, vcf 31) (rho_sub rho s_ent) tp); [left; reflexivity | exact (phi_sub V_ldR ldefR ldefR_reads s_ent rho CidV HPHI) |].
  rewrite efmeas_z0, efmeas_vcf. pose proof (uval_range (rho_sub rho s_ent) (vcf 31)) as RV. lia.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S1eS11VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S9dS11S9cVAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.

Hypothesis CONT_RP_T : ltac2:(tb__ "0|1|
S1fS2S2bQ40A1A1M0G0S45R3A1S4bS11Vok;S2fS11VJAv;S59A1S58R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").

Lemma CVRN_T : ltac2:(tb__ "0|1|
S2S1SdSdA2M0A1S2S1G0SdA2A1S41S1fS2S2bQ40A1A1S40Z3R3A2S4bS11Vok;S2fS11S14VAInv;VCST;VXGL;VKc;S52R6R5A2R6R5R4S13S93S8bS4S8dA3AaS8cR3R2A5S81S11S8eR3R2S94VAInv;VCST;VXGL;VKc;S52S13S60R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k segs AInv CST XGL Kc VRNP.P0_vr PTrue VRN.Pre_vr (ndh h0 true VRN.nd0) (PDh PD_vr h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc VRNP.P0_vr PTrue VRN.Pre_vr VRN.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (VRNP.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Let famS (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
SdS2S2bQ40A1A1S4cS2eSaaS11S48S3aSa7S3eVAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S13S44AcS48S39S3aS3cS54A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|5|
S2S2bQ40A1A1M0SeS12S3S1SdS20A2M1S1fG0SdG0S4dS1S1S1SeS12A2M2S3A2M3G1A2S0G3G1S0G2S3S0SeS12R8R7A4R6A4R5A4S54A3S38S44R7R5A3S2dS32Z0S37S0G3G1S0G2S3S0SeS12RaR9A4R8A4R7A4R6A2M4A2S33G4R4A2A2S4bS11Vok;S2fS11VJAv;RaA1RbR7R6A5VfamS;RcR5R4A3A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;").
Proof.
  intros tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS ok (map efdrop cutsCF) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S2S2bQ40A1A1M0S49SdG0S4bS11Vok;R3VFAMQ;R4A1A4S4bS11Vok;R4VfamS;R5R3R2A3A4F_;Ftp0';Fb;FP;Ftp0;").
Proof. intros tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma CF_T : ltac2:(tb__ "0|4|
SeS12S3S1SdS20A2M0S1fS2S2bQ40A1A1M1G1S4dS1S1S1SeS12A2M2S3A2M3G0A2S0G3G0S0G2S3S0SeS12R7R6A4R5A4R4A4S54A3S38S44R6R4A3S4bS11Vok;S2fS11VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertCF_ok 600%nat cps_cf NP cutsCF exitsCF ok (FAMQ tp0) Hok
           ecertCF_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsCF_ok (triple segs ok) (famS tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CVRN_T (reenterS tp0)
           (fun rho tp b tp0' HL _ => rightS tp0 _ b tp0' (CONT_RP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiCF_T : ltac2:(tb__ "0|1|
S1fS2S2bQ40A1A1M0G0S45R3A1S4bS11Vok;S2fS11VJAv;S56A1S57R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) ok nd_succ L_cf0 rho tp _ HL).
  exact (X_L_cf0 (triple segs ok) (fun _ tp0' => FAMQ tp0') (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => CF_T T nd k rv rho tp tp0' Hi Hp) rho tp tp0).
Qed.

Theorem epiCF_TF : ltac2:(tb__ "0|1|
S1fS2S2bQ40A1A1M0G0S4bS11Vok;S2fS11VJAFv;S38S44U0A2S56A2S57R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) ok nd_succ L_cf0 rho tp). intros HL. exact (epiCF_T rho tp tp0 HL).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S9eS11S9cVAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
SdS2S2bQ40A1A1S49F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SdSdS2S2bQ40A1A1S4cS32R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis CONT_RP_E : ltac2:(tb__ "0|1|
S1fS2S2bQ40A1A1M0G0S45R3A1S4aS11S2fS11VJAv;S59A1S58R4R3A5VFAM;S35S34Z187S36Z2Z40A2A2Z37fA2R2A2A3F_;Ftp0;Ftp;Frho;").
Lemma rp_le : ltac2:(tb__ "0|4|
S1fSdS2dS32Z0S37S0S1S1SeS12A2M0S3A2S1SdS20A2S0G0S3S0SeS12S58S59A4U0A4S0SdS20Z187M1S23Z37fM2A1A4A4R2A2M3A2S33G3R1A2A2S32S35S34G1S36Z2Z40A2A2G2A2R2A2F_;Fb;Frho;").
Proof using . intros rho b H. rewrite efmeas_lit in H by lia. lia. Qed.

Lemma CVRN_E : ltac2:(tb__ "0|1|
S2S1SdSdA2M0A1S2S1G0SdA2A1S41S1fS2S2bQ40A1A1S40Z3R3A2S4aS11S2fS11S14VAInv;VCST;VXGL;VKc;S52R6R5A2R6R5R4S13S93S8bS4S8dA3AaS8cR3R2A5S81S11S8eR3R2S94VAInv;VCST;VXGL;VKc;S52S13S60R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc VRNP.P0_vr PTrue VRN.Pre_vr (ndh h0 true VRN.nd0) (PDh PD_vr h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc VRNP.P0_vr PTrue VRN.Pre_vr VRN.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (VRNP.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Let famE (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
SdS2S2bQ40A1A1S4cS2eSa9S11S48S39Sa6S3dVAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S13S44AcS54A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|5|
S2S2bQ40A1A1M0SeS12S3S1SdS20A2M1S1fG0SdG0S4dS1S1S1SeS12A2M2S3A2M3G1A2S0G3G1S0G2S3S0SeS12R8R7A4R6A4R5A4S54A3S38S44R7R5A3S2dS32Z0S37S0G3G1S0G2S3S0SeS12RaR9A4R8A4R7A4R6A2M4A2S33G4R4A2A2S4aS11S2fS11VJAv;RaA1RbR7R6A5VfamE;RcR5R4A3A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;").
Proof.
  intros tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS cutsCF T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S2S2bQ40A1A1M0S49SdSdG0S32R3R2A2S4aS11R5VFAM;R4R6A2A3S4aS11R6VfamE;R7R4R3A3A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;").
Proof. intros tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma CF_E : ltac2:(tb__ "0|4|
SeS12S3S1SdS20A2M0S1fS2S2bQ40A1A1M1G1S4dS1S1S1SeS12A2M2S3A2M3G0A2S0G3G0S0G2S3S0SeS12R7R6A4R5A4R4A4S54A3S38S44R6R4A3S4aS11S2fS11VJAv;R8A1R9R5R4A5VFAM;S37S0G3G0S0G2S3S0SeS12R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertCF_ok 600%nat cps_cf NP cutsCF exitsCF (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertCF_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsCF_ok (etriple segs) (famE tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CVRN_E (reenterE tp0)
           (fun rho tp b tp0' HL Hm => rightE tp0 _ _ b tp0' (rp_le rho b Hm) (CONT_RP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Lemma cutE : ltac2:(tb__ "0|5|
SeS12S3S1SdS20A2M0S1fS2S2bQ40A1A1M1SdG1S4dS1S1S1SeS12A2M2S3A2M3G0A2S0G3G0S0G2S3S0SeS12R8R7A4R6A4R5A4S54A3S38S44R7R5A3S2dS32Z0S37S0G3G0S0G2S3S0SeS12RaR9A4R8A4R7A4R6A2M4A2S33G4R4A2A2S4aS11S2fS11VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hi Hp Hm.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w (Z.lt_le_incl _ _ (proj2 Hm)) Hw) | exact (CF_E T nd k rv rho tp tp0' Hi Hp)].
Qed.

Theorem epiCF_E : ltac2:(tb__ "0|2|
S1fS2S2bQ40A1A1M0G0S45R3A1S4aS11S2fS11VJAv;S56A1S57R4R3A5VFAM;S37S0S1S1SeS12A2M1S3A2S1SdS20A2S0G1S3S0SeS12S57S56A4U0A4S0SdS20Z18aS7aA4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) nd_succ L_cf0 rho tp _ HL).
  exact (X_L_cf0 (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           cutE rho tp tp0).
Qed.
Theorem epiCF_EF : ltac2:(tb__ "0|3|
S1fS2S2bQ40A1A1M0G0S4aS11S2fS11VJAFv;S38S44U0M1A2S56A2S57R3R2A5VFAM;S37S0S1S1SeS12A2M2S3A2S1SdS20A2S0G2S3S0SeS12S57S56A4G1A4S0SdS20Z18aS7aA4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) nd_succ L_cf0 rho tp). intros HL. exact (epiCF_E rho tp tp0 HL).
Qed.
End Existence.
End Sum.

