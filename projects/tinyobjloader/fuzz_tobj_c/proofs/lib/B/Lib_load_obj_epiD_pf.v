(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "bool"; "true"; "nil"; "cons"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "holds"; "sobj"; "SLit"; "sprop_eqb"; "SPUle"; "eval"; "ss_next"; "ss_objs"; "sv_eqb"; "SPBranch"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "NDA"; "amode"; "TPA"; "frinA"; "tvinA"; "JA"; "JA_pre"; "fbinA"; "ffinA"; "JAi"; "tvals"; "untrackedZ"; "ANone"; "nd_am"; "ok_frameKA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "True"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "xrs47_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "PhisD"; "nd_d2"; "gp"; "nd_d1"; "nd_d0"; "nd_z"; "nd_e"; "cutsD1"; "cutsD2"; "cutsD3"; "ndT"; "nd_A2"; "nd_B2"; "nd_CL"; "nd_fa"; "exitsD1"; "exitsD2"; "exitsD3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "extraLO"; "ldef"; "@Stdlib.Lists.List"; "In"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BXok_d"; "bxt"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "L_ms"; "Pre_ms"; "vF"; "vFL"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_pf.BDP"; "P0_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tnz"; "tvd"; "T_ok"; "tvv"; "tvz"; "FBx"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "JL_pure"; "AE_A"; "UStopLe"; "JL_free"; "JL_stack_free"; "J_free_pre"; "J_memset_pre"; "J_pure_pre"; "J_stack_free_pre"; "V_FL"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "L_ok"; "vG"; "E_fa0"; "E_fd0"; "E_ml0"; "E_s80"; "L_L1"; "L_L3"; "X_A"; "X_B"; "X_fa0"; "X_fa1"; "vNx";
"nB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD3"; "P_errL"; "L_sf"; "Pre_sf"; "Ee_sf"; "Ee_sf0"; "Ee_zf"; "Te_s82"; "X_sx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "kept_bd"; "K_disp"; "L_fr"; "PDk_bd"; "Pre_fr"; "E_bd0"; "L_j1s"; "Lb_j1"; "R_bd"; "E_bd"; "E_flG"; "PD_bd"; "Xk_bd"; "passed_bd"; "s_bd"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "W2"; "L_f8"; "Pre_f8"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1.BD"; "NP"; "Pre_bd"; "ndL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "extraXlo"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pdescA"; "robjs_okF"; "pclMA"; "robjs_okL"; "xrs_okF"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "site_okA"; "cmaddrA"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_chk"; "ent_chk"; "two52"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "add"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3 Lib_load_obj_epiD_eqs Lib_load_obj_epiD_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BDP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_builder_dispose_pf. End BDP.

Lemma h0_ltBD : (h0 < BD.NP)%positive. Proof. reflexivity. Qed.
Lemma efmeas_z0 : ltac2:(tb__ "0|1|
SfS24S3S12S15S3aS12S41S0S1S1SfS24A2M0S3A2S1S12S14A2S0G0S3S0SfS24R5R4A4R3A4S0S12S14R2S6aA4A4R1A2S72R2S73Z2Z40A2A2A3Frho;Fr;Fk;Fnd;FT;").
Proof. intros. unfold efmeasA, ef_rank, ef_var, z0. cbn [fst snd]. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

Lemma tvd_nth_remove : ltac2:(tb__ "0|1|
S15S2S1S14S14A2M0A1S3G0G0S8aR5R4A2S3aSaG0A1S65G0R5R4A3S8G0R3A2A3S64G0R3S88G0R5R6A3A3S89R8R5A2S89R9R5A2S3dS3aS1S12S12A2S8cRaR7A2S8cRaR6A2A3A1F_;F_;F_;F_;F_;Ft';Ft;Fi;Ftv;Frho;").
Proof.
  intros rho tv. induction tv as [|h r IH]; intros [|i] t t' HD Hn Hin Hz Hz'; cbn in Hn, Hin; try discriminate; try contradiction.
  - injection Hn as ->. destruct HD as [H _]. exact (H t' Hin Hz Hz').
  - destruct HD as [H HD']. destruct Hin as [<-|Hin].
    + intros E. exact (H t (nth_error_In _ _ Hn) Hz' Hz (eq_sym E)).
    + exact (IH i t t' HD' Hn Hin Hz Hz').
Qed.

Section DropTv.
Variable AInv : ltac2:(tb__ "0|0|
S67S15S2S35Q40A1A1S74OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1S12S12A2S12A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Lemma untrackedZ_remove_null : ltac2:(tb__ "0|1|
S15S2S1S14S14A2M0A1S3S1S12S12A2G0S3aSaG0A1S65G0R4R3A3S8G0R1A2A3S3dS89R6R2A2A1F_;Ft;S40S31S30R5R4A2R2A2S31S30R5S88G0R3R4A3A2R2A2A2F_;Fbn;Fi;Ftv;Frho;").
Proof.
  intros rho tv i bn HNULL. unfold untrackedZ, tvals. split.
  - intros H v Hv Hnz. apply in_map_iff in Hv as (t & <- & Ht). apply H; [apply in_map; exact (remove_nth_In _ _ _ Ht) | exact Hnz].
  - intros H v Hv Hnz. apply in_map_iff in Hv as (t & <- & Ht).
    destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.In_remove_nth_or tv i t Ht) as [E|E]; [exfalso; exact (HNULL t E Hnz)|].
    apply H; [apply in_map; exact E | exact Hnz].
Qed.
Lemma JAi_drop_tv_am : ltac2:(tb__ "0|1|
S2S1S14S14A2M0A1S2S1S1S14S12A2S14A2A1S2S78A1S27S3S67S12S15S2S35Q40A1A1S2S75A1S74G0S3aSaG0A1S65G0RcR8A3S8G0R1A2A3S3dS89R6R2A2A1F_;Ft;S2fVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26RcRbRaR9A4R7R6R5R4R3R2A12S2fVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26S88G0R9RdA3RcRbRaA4R8R7R6R5R4R3A12F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fi;Fam;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd am i Ai kc rho tp tr md HNULL (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am] in *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|split; [exact HPA|split; [exact HCK|
    unfold capN in *; cbn [nd_tv]; rewrite (cntS_remove_nth_null rho tv i HNULL); exact HCN]]]]]]]].
  - split; [|split].
    + unfold tvinA in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). eapply remove_nth_In. exact Ht.
    + apply tvd_remove. exact HD.
    + unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht.
  - unfold XA in *.
    refine (proj1 (XAz_transport FB FB (am_eval rho am) Ai Ai (rm rho) (rm rho) (tvals rho tv) (tvals rho (remove_nth i tv)) kc HXA _ _ _ _)).
    + intros b n H1 H2 H3. split; [exact H1|]. split; [exact H2|]. exact (proj1 (untrackedZ_remove_null rho tv i (b, n) HNULL) H3).
    + intros; reflexivity.
    + intros b n a _ _ _ _. split; [intros _; reflexivity | intros j _ H; exact H].
    + intros bn H1 _ H3 H4. split; [exact H1|]. split; [exact H3|]. exact (proj2 (untrackedZ_remove_null rho tv i bn HNULL) H4).
Qed.
Variable segs' : list Segment.
Lemma SPA_JA_drop_tv_am_fact : ltac2:(tb__ "0|1|
S2S1S14S14A2M0A1S2S1S1S14S12A2S14A2A1S2S78A1S27S3SfS15S2S35Q40A1A1S6eG0S3aSaG0A1S65G0RaR6A3S8G0R1A2A3S3aS4S66S16S1bS21Se8S9S14S14R2A3S1aZ0A1A3A1S17S10R6A1A1A3S5A3F_;Ft;S37Vsegs';S2bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26RaR9R8R7A4AcR5R4R3R2A6S37Vsegs';S2bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26S88G0R7RbA3RaR9R8A4AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FS;Fi;Fam;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd am i S rho tp [tr [ms md]] HZ [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  apply JAi_drop_tv_am; [|exact HJ]. intros t Ht Hnz.
  pose proof (smatchA_facts segs' _ _ _ _ Hsm) as HF.
  pose proof (holds_mem _ _ _ HF (HZ t Ht)) as X. apply (proj1 (holds_beq _ _ _)) in X.
  unfold tnz in Hnz. rewrite X in Hnz. apply Hnz. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). apply uval_lit. lia.
Qed.
End DropTv.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S67S15S2S35Q40A1A1S74OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S9dS23VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S12Sd5VCST;R1A2S3bS6fZ0R2A2S70R2Se7A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S12Sd5VXGL;R1A2S3bS6fZ0R2A2S70R2Se7A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S12SebR1A1Sd5VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1S12S12A2S12A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S15OFr;") := ltac2:(tb__ "0|0|
SeeVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBX;S25Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S45VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBX;S25VPhi;Vnd;Ad").

Lemma lo_robjsF0 : ltac2:(tb__ "0|0|
S67S15S2S16A1S2S1S14S14A2A1S2S19A1S15S2S35Q40A1A1S74VAInv;R8R3R2R1A4S81S16S18R8A1R7A3VP0;Vrho0;A1Sb5S7cVrho0;RaA3S28Vrho0;RcA2S8bRcS69S68RdA1A1A2S2aVFB;ReRdRbA4S8aReRcA2S8dRfRdA2S29VFF;R11R10S61A4S3aS4SccR10RfS61S62ReA5S5A3SdcVCST;Vrho0;VFB;VFF;R12R10S61RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
Qed.
Lemma lo_robjsR0 : ltac2:(tb__ "0|0|
S67S15S2S16A1S2S1S14S14A2A1S2S19A1S15S2S35Q40A1A1S74VAInv;R8R3R2R1A4S81S16S18R8A1R7A3VP0;Vrho0;A1Sb5S7cVrho0;RaA3S28Vrho0;RcA2S8bRcS69S68RdA1A1A2S2aVFB;ReRdRbA4S8aReRcA2S8dRfRdA2S29VFF;R11R10S61A4S3aS4Sd6R10RfS61S62ReA5S5A3Se4VCST;Vrho0;VFB;VFF;R12R10S61RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkR_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
Qed.

Lemma site_rt_lo0 : ltac2:(tb__ "0|0|
SfS87S2S19A1S15S2S1S14S14A2A1S2S78A1S27S3aS4SccS17S10R7A1A1R3S61S62R5A5S5A3S3aS4SceS17S10R8A1A1R4S61ScdS11R8A1A5S5A3Se1VAInv;VCST;VXGL;S7cVrho0;VP0;VFB;VFF;R9R8R7R6S26R5S61R4R3A4SdS12A1S67S8fS3fL_;L_;AfF_;F_;Fam;Fbd;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv bd am CR CX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (lo_robjsF0 Ai rho _ tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR) as HRF.
  pose proof (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tv (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX) as HXF.
  assert (HN' : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.fbinA_FBx FB Ai rho tv [] HBf HN') as FBX. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.ffinA_FFx FF Ai rho frL HFF HFR) as FFX.
  split; [|split; [|exact I]].
  - intros o a Ho Hr. eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact (HRF o a Ho Hr)].
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact Hc].
Qed.

Lemma pclMA_cmaddrA_x : ltac2:(tb__ "0|1|
S67S15S2S1S14S14A2M0A1S3G0S12S15S2S35Q40A1A1S74VAInv;R9R3R2R1A4S2dVFB;RaA2S2eVFF;RbA2S28Vrho0;RcA2S2aVFB;RdRcRbA4S8aRdRcA2S29VFF;RfReS61A4S3aSaG0A1S65G0ReRdA3S8G0RcA2A3S89R10RdA2SddVCST;Vrho0;S8eVFB;R11S88G0RfR10A3A3SdaVFF;R11S61A3RdA5Se2VCST;R13S8S12S9S12S12S8cR12RfA2A3A2ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;Fa;Ft;Fi;Ftv;Frho;FAi;").
Proof using ALA.
  intros Ai rho tv i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hz Hp.
  pose proof (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hn) Hz) as (_ & HtL & HtF).
  destruct Hp as [Hs | [Hc | [(b & n & Hin & Hr) | (f & s & fl & Hin & Hr)]]].
  - left. destruct HT as [_ HT2]. rewrite HT2. exact Hs.
  - right. left. exact Hc.
  - right. right. left. exists b, n.
    assert (HbL : In (b, n) (aa_live Ai) /\ (b, n) <> tvv rho t).
    { apply In_FBx in Hin as [Hin|(t' & Ht' & Hz' & E)].
      - split; [exact (HBf _ Hin)|]. intros E. apply HtF. rewrite <- E. exact Hin.
      - split.
        + rewrite <- E. exact (proj1 (proj2 (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hz'))).
        + rewrite <- E. intros E'. exact (tvd_nth_remove rho tv i t t' HD Hn Ht' Hz Hz' (eq_sym E')). }
    destruct HbL as [HbL Hne]. split; [exact HbL|]. split; [|exact Hr].
    intros E. assert (E' : b = fst (tvv rho t)) by congruence.
    apply (blocks_bases_differA segs AInv CST ALA Ai rho1 tp1 md1 b n (fst (tvv rho t)) (snd (tvv rho t)) HM HbL);
      [rewrite <- surjective_pairing; exact HtL | rewrite <- surjective_pairing; exact Hne | exact E'].
  - right. right. right. exists f, s.
    destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.ffinA_FFx FF Ai rho frL HFF HFR f s fl Hin) as [H _]. split; [exact H | exact Hr].
Qed.

Lemma site_free : ltac2:(tb__ "0|3|
SfS87S2S19A1S15S2S1S14S14A2M0A1S3G0S2S78A1S27S3aSaG0A1S65G0R5R4A3S8G0R3A2A3S3aS4SccS17S10RaA1A1S88G0R5R6A3S61S62R8A5S5A3S3aS4SceS17S10RbA1A1S88G0R6R7A3S61ScdS11RbA1A5S5A3S3aS4S20S9S14S14R6A3S84RbPcM1A2A2S5A3S3aS4S20ScS14S14R7A3S84RcPdM2A2A2S5A3S81S16S18RbA1S17S10ReA1A1A3S89RcR9A2F_;Se1VAInv;VCST;VXGL;S7cVrho0;VP0;VFB;VFF;RfReRdRcS26RbS61R8R7A4S8S12S77RcS84ReG1A2A2A2S67S8fS3bS89ReRbA2S3bS3aS1S12S12A2S8cReRbA2S0S12S12S77ReS84R10G1A2A2S77ReS84R10G2A2A2A4A3S9eSc7S93S86S85ReRfR1A3R10A2A3A2A2Lms;LAi;AfF_;F_;F_;F_;F_;F_;Fam;Fbd;Ft;Fi;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv i t bd am Hn CR CX H12 H13 Hnzf Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13. rewrite <- H12, <- H13.
  pose proof (Hnzf HF) as Hnz.
  assert (HNr : tvinA FB Ai rho (remove_nth i tv)) by (apply (tvinA_sublist FB Ai rho tv); [intros x Hx; exact (remove_nth_In _ _ _ Hx) | exact HN]).
  assert (HDr : tvd rho (remove_nth i tv)) by (apply tvd_remove; exact HD).
  assert (HZr : tvz rho (remove_nth i tv)) by (apply (tvz_sublist rho tv); [intros x Hx; exact (remove_nth_In _ _ _ Hx) | exact HZ]).
  pose proof (lo_robjsF0 Ai rho _ _ R rho1 tp1 md1 HM HF HP0 Hav HT HTK HNr HDr HZr HFR CR) as HRF.
  pose proof (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ _ (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HNr HDr HZr HFR CX) as HXF.
  split; [|split; [|split; [exact Hnz | split; [reflexivity | exact I]]]].
  - intros o a Ho Hr. exact (pclMA_cmaddrA_x Ai rho tv i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hnz (HRF o a Ho Hr)).
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    exact (pclMA_cmaddrA_x Ai rho tv i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hnz Hc).
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S2S16A1S2S78A1S3aS4S7bR1A1S5A3Se3S7cVrho0;VP0;R3S1aZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Lemma szL_val : ltac2:(tb__ "0|0|
S15S2S16A1S81S16S18R2A1R1A3S3aS4S66S16S1bS1cSd9S1aZffffffffA1A2A1R2A3S5A3S3aS12S77R4Sc6A2S72Z10S77R4Sd9A2A2A3F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF C. pose proof (holds_mem _ _ _ HF C) as H. rewrite h_ule, uval_lit in H by lia.
  pose proof (uval_range rho xLK) as R. unfold szL, kb. apply uval_mul_lit; lia.
Qed.

Lemma HIN_bd : ltac2:(tb__ "0|1|
S15S8fS67S15S2S35Q40A1A1S74S81S16S18R6A1S17S10Sc0A1A1A3VP0;Vrho0;A1Sb5S7cVrho0;R8A3VAInv;R7R6R5R4A4S28Vrho0;R8A2S8bRbS69S68R9A1A1A2S2dVFB;RaA2S2eVFF;RbA2S2aVFB;RcReSeS1S14S14A2Sb7Sc4A3M0A4S8aRfG0A2S8dR10G0A2S29VFF;RfR11S61A4S3bSdcVCST;Vrho0;VFB;VFF;R12Sb7S61SbfA8S3bSdfVCST;VXGL;Vrho0;VFB;VFF;R12Sb7S61Sc3A9S83S8eVFB;R12Sb7A3SdaVFF;R12S61A3S86S85R12SbfR11A3Sc5A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof epiD_chk_bd as (CR & CX & _ & _ & _ & _ & _ & F5 & _).
  assert (HNk : tvinA FB Ai rho kept_bd) by (apply (tvinA_sublist FB Ai rho (kept_bd ++ passed_bd)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_bd) by (exact (tvd_app_l rho kept_bd passed_bd HD)).
  assert (HZk : tvz rho kept_bd) by (apply (tvz_sublist rho (kept_bd ++ passed_bd)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF0 Ai rho _ kept_bd R_bd rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_bd Xk_bd rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold BDP.P0_bd. rewrite !rw_call'.
    change (wsub_get s_bd 12) with bA. change (wsub_get s_bd 16) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    pose proof (holds_mem _ _ _ HF F5) as HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6dF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S38SfS15S2S35Q40A1A1S6dS81S16S18R3A1S17S10R4A1A1A3VTR;S37S23R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S6dS6dS6dS6eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S6dOS6dS6eR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S38S38SfSfS87S2S19A1M0S2S1SfS5cA2M1A1S2S1S14S14A2M2A1S6dS15S2S35Q40A1A1M3G2S64G2R1R5A3S64G2R2S11RbA1A3F_;Fr;S3aSaG0A1S60RaR9R8A3S8G0R7A2A3S3aS4S5fRbRaR9R8S82G1SfS9SfS5cA2R7A4A5S5A3S15G3VTR;S37S23RfRdR2R1A5S5dS23S1eS10RdA1A1R2R1RaA5A2Ftp1;Frho1;S2S75A1M4S8fS74S39S23R9R8R10S0G4ScaR3ScbR2R1A2A4A5R13RaR9R4R2A4R13S86S85RbRfS90R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SfS5cG4S8fS74S15G3G4S8fS74S64G1S0SfS5cRaR9A4R14A3S39S23R12R11R19S0G4ScaR9ScbR8R7A2A4A5R1cR13R12RaR8A4Sb5S1eS10R1aA1A1S86S85R14R18S90R9R13RaA3A3R19A2R8A3S39S23R9R8ReS0G4ScaR7ScbR6R5A2A4A5ReS86S85R16R1aS90RbR15RcA3A3R1bA2R15RaR9R8R6A6S3bSf3R17S90RcR16RdA3R1bR1cR1dR10R1eR19RbA9S15Sb6R18S90RdR17ReA3R1cR1dS10R1eA1S10R1fA1S10R11A1R1RcA9VTR;S37S23S5eR11S86S85R19R1dS90ReR18RfA3A3R1eA2R18RdRcA5Sf4R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S37S23R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S15OF_;S24SfS15S2S35Q40A1A1S6dR6R3A1VTR;S37S23VJAv;R6A1R5R4R3A5R2A2F_;VTR;S37S23VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CBD : ltac2:(tb__ "0|1|
S2S1S12S12A2M0A1S2S1G0S12A2A1S7aS15S2S35Q40A1A1S79Z5R3A2VTR;S37S23S2cVAInv;VCST;VXGL;VKc;S83R6R5A2R6R5R4S25Sd3ScfSbSd2U0A1A3AaSd1R3R2A5S5dS23Sd0R3R2Sd4VAInv;VCST;VXGL;VKc;S83S25SbaR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CFREE : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1VTR;S37S23S96VAInv;Sc7S93R3VKc;A5SbbR2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cSb9S94VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CUT1 : ltac2:(tb__ "0|5|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1S12G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4S51A3S42S4aR7R5A3S3bS6fZ0S41S0G3G0S0G2S3S0SfS24RaR9A4R8A4R7A4R6A2M4A2S70G4R4A2A2VTR;S37S23VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUT2 : ltac2:(tb__ "0|5|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1S12G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4S52A3S42S4aR7R5A3S3bS6fZ0S41S0G3G0S0G2S3S0SfS24RaR9A4R8A4R7A4R6A2M4A2S70G4R4A2A2VTR;S37S23VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma X_E_bd0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU0M1A2S4eA2SbcR3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24SbcS4eA4G1A4S0S12S14Z185S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldef rho) in HPHI.
  pose proof epiD1_checks_bd as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cxk & Chand & Chb & Cnb & Cbr & Cnp & CT0 & CB & Ctidy & Cwf & Ckept & Cktv & Cbd' & Cam' & _).
  pose proof epiD_chk_bd as (CR & CX & Cwp & F1 & F2 & F3 & F4 & F5 & F6 & CVb).
  apply (TR_pre (SPA segs (JAv (ndEp tv_bd bd_disp)) E_bd rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv (ndEp tv_bd bd_disp)) xf_bd rho E_bd0 E_bd tp w Cxf).
    unfold ndEp. apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL tv_bd frL bd_disp (AHead pH false) E_bd0 rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndEp] in HZ. intros E0.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [unfold tv_bd; apply in_or_app; left; rewrite Ckept; left; reflexivity|].
    unfold tnz. cbn [fst]. intros H. exact (H E0). }
  intros Hnull.
  unfold ndEp, tv_bd.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX BDP.P0_bd PTrue (fun _ H => H) (fun _ _ _ H => H)
           BD.Pre_bd (ndh h0 false (BD.ndL 0)) PDk_bd BD.NP eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CBD eq_refl
           E_bd s_bd R_bd Xk_bd rho tp kept_bd passed_bd frL bd_disp brest_bd (AHead pH false) (FAM (efmeasA (E_bd0, nd_d0, 0%nat, (389, z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand, Chb. apply payA_same. exact Cwp.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_bd rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndLd] PsiL] rho' tp' Hd Hag HK _.
    cbn [PDk_bd liftPD PDh PD_bd map In fst snd] in Hd. destruct Hd as [Hd|[]]. injection Hd as <- <- <-. cbn [fst snd].
    rewrite Cktv, Cbd', Cam', CT0.
    apply (TR_pre (SPA segs (JAv nd_d1) T_bd rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_d1) xfb_bd rho' T_bd0 B_bd tp' w CB Hw). }
    apply (CUT1 T_bd nd_d1 0%nat (380, z0) rho' tp'); [right; left; reflexivity | | rewrite !efmeas_z0; lia].

    change (ldef rho').
    assert (E466 : uval rho' xLD = uval rho xLD) by (apply (uval_rw rho rho' 466 xLD eq_refl); apply (proj1 Hag); reflexivity).
    assert (E468 : uval rho' xLK = uval rho xLK) by (apply (uval_rw rho rho' 468 xLK eq_refl); apply (proj1 Hag); reflexivity).
    pose proof (szL_val rho _ HF F2) as ESZ.
    intros z Hz. rewrite E466, E468 in Hz.
    destruct (Z.eq_dec (uval rho xLD) 0) as [E0|Hnz]; [pose proof (Hnull E0); lia|].
    pose proof (holds_mem _ _ _ HF F3) as H3. rewrite h_ule, uval_lit in H3 by lia.
    pose proof (holds_mem _ _ _ HF F1) as H1. rewrite h_ule, uval_lit in H1 by lia. fold szL in H1.
    pose proof (holds_mem _ _ _ HF F4) as H4. rewrite h_ule in H4. fold szL in H4.
    pose proof (holds_mem _ _ _ HF F6) as H6. rewrite h_ule, uval_lit in H6 by lia.
    rewrite (uval_add_small rho xLD szL) in H4 by lia.
    rewrite (keptK_lines CST FB FF rho0 rho kept_bd frL rho' HK ltac:(rewrite Ckept; left; reflexivity) Hnz ltac:(lia) ltac:(unfold B32, Lib_vec_reserve.B32; lia) z Hz).
    exact (HPHI z Hz).
Qed.

Lemma X_L_j1s : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU0M1A2S4dA2SbdR3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24SbdS4dA4G1A4S0S12S14Z17bS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_j1 as (C1 & _ & Crm). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD1_checks_j1 as (_ & _ & _ & _ & _ & Cz).
  pose proof epiD1_checks_fl as (_ & _ & _ & _ & _ & _ & _ & Cnth & _).
  apply (TR_pre (SPA segs (JAv nd_d2) K_j1 (rho_sub rho s_j1s) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_j1s K_j1 s_j1s nd_d1n nd_d2 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    unfold nd_d1n, ndEp. rewrite <- Crm.
    apply (SPA_JA_drop_tv_am_fact AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue segs kept_bd frL brest_bd (AHead pH false) 0%nat L_j1s rho tp w); [|exact Hw].
    intros t Ht. rewrite Cnth in Ht. injection Ht as <-. exact Cz. }
  apply (CUT2 K_j1 nd_d2 1%nat (360, z0) (rho_sub rho s_j1s) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_Lb_j1 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4bA2SbeR3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24SbeS4bA4G1A4S0S12S14Z171S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_j1 as (_ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_d2) K_j1 (rho_sub rho s_j1b) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lb_j1 K_j1 s_j1b nd_d2 nd_d2 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUT2 K_j1 nd_d2 1%nat (360, z0) (rho_sub rho s_j1b) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_L_fl : ltac2:(tb__ "0|3|
SfS15S2S35Q40A1A1M0G0S3aS4SecR4Sc1S6S1S13S14A2A1S4dS4dA5S5A3VTR;S37S23VJAFv;S42S4aU0M1A2S4dA2R5R4R3A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24R5S4dA4G1A4S0S12S14Z17bS6aA4A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FL;").
Proof.
  intros L rho tp tp0 CE. apply TR_JAF. intros HPHI. change (ldef rho) in HPHI.
  apply ent_chk_unf in CE as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD_chk_fl as (_ & _ & CidV & F1 & F2 & Csite & Ccarve & CdX & Ffsz & CR & CX & Fdnz & Cpay & Cbb & CT0 & Crm).
  pose proof epiD1_checks_fl as (_ & _ & CflF & Cfb & Fdnz0 & CwfC & Cbase & Cnth & CwfE & Cent & Cchk & Cta & Cnp' & Cnb' & C12 & C13 & Ctidy & CwfT & _).
  set (rho1 := rho_sub rho []).
  assert (HPHI1 : ldef rho1) by (exact (phi_sub V_ld ldef ldef_reads [] rho CidV HPHI)).
  apply (TR_pre (SPA segs (JAv nd_d1) E_flG rho1 tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L E_flG [] nd_d1 nd_d1 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply TR_facts. intros HFG.
  pose proof (szL_val rho1 _ HFG F2) as ESZ.
  apply (TR_pre (SPA segs (JAv nd_d1) E_fl rho1 tp)).
  { intros [tr [ms md]] Hw.
    assert (HwF : SPA segs (JAv nd_d1) E_flF rho1 tp (tr, mkCfg ms md)).
    { rewrite <- CflF. apply (SPA_refacts_JA segs _ rho1 _ _ tp _ Hw Cfb).
      intros tr' md' HJ _. apply Forall_app. split; [|exact HFG]. constructor; [|constructor].
      destruct HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (HN & _ & _) & _). cbn [nd_tv nd_d1 ndEp] in HN.
      pose proof (holds_mem _ _ _ HFG Fdnz0) as Hd. apply (proj1 (holds_nbeq _ _ _)) in Hd.
      change (bv_unsigned (eval rho1 (SLit 0))) with (uval rho1 (SLit 0)) in Hd. rewrite uval_lit in Hd by lia.
      destruct (proj1 (Forall_forall _ _) HN (xLD, szL) (nth_error_In _ _ Cnth) Hd) as (Hpos & _).
      unfold fact_sz. rewrite h_ule, uval_lit by lia. unfold tvv in Hpos. cbn [snd] in Hpos. change (bv_unsigned (eval rho1 szL)) with (uval rho1 szL) in Hpos. lia. }
    rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0)|].
    rewrite <- Ccarve.
    refine (proj1 (JA_carve_tr segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HNP kept_bd frL brest_bd (AHead pH false) 0%nat xLD szL xLD szL E_flF rho1 tp tr ms md
                     Cnth Cbase ltac:(rewrite Ccarve; exact CwfC) _ _ _ HwF)).
    - intros r HFr. pose proof (holds_mem _ _ _ HFr Ffsz) as Hs. unfold fact_sz in Hs. rewrite h_ule, uval_lit in Hs by lia. lia.
    - apply (carve_site_chk_sound segs AInv CST ALA HCST NP rho0 P0 FB FF E_flF kept_bd frL 0%nat extraLO rho1 Csite).
      intros Ai tp1 md1 _ HP0 Hav _ _ _ _ _ _ _ _ _ o a Ho HE Hr. left. exact (extraLO_pclMA CST rho0 FB FF rho1 _ frL o a Hav HP0 HE Hr).
    - intros z Hz. apply HPHI1. rewrite <- ESZ. exact Hz. }
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           W2 UStopLe E_fl s_fl R_fl rho1 tp nd_d1 0%nat (xLD, szL) KU1 (FAM (efmeasA (L, nd_d1, 0%nat, (379, z0)) rho) tp0) CFREE
           Cent Cchk Cta Cnp' Cnb' Cbb Cnth).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fl s_fl R_fl rho1 kept_bd 0%nat (xLD, szL) brest_bd (AHead pH false) Cnth); [rewrite Crm; exact CR | rewrite Crm; exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. pose proof (holds_mem _ _ _ HFE Fdnz) as Hd. apply (proj1 (holds_nbeq _ _ _)) in Hd.
    change (bv_unsigned (eval rho1 (SLit 0))) with (uval rho1 (SLit 0)) in Hd. rewrite uval_lit in Hd by lia. exact Hd.
  - intros rho' tp' _ _. cbn [nd_tv nd_fr nd_am nd_d1 ndEp]. unfold Pre_fr, L_fr in CT0. rewrite Crm, CT0.
    apply (TR_pre (SPA segs (JAv nd_d2) T_fl rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT1 T_fl nd_d2 1%nat (370, z0) rho' tp'); [right; right; left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Hypothesis CUT3 : ltac2:(tb__ "0|5|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1S12G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4S53A3S42S4aR7R5A3S3bS6fZ0S41S0G3G0S0G2S3S0SfS24RaR9A4R8A4R7A4R6A2M4A2S70G4R4A2A2VTR;S37S23VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma popN_site : ltac2:(tb__ "0|1|
S2S1S14S14A2A1S2S78A1S27SfS15S2S35Q40A1A1S6eS37S23VJAv;S26R7S61R6R5A4A1R4R3R2R1A6S3aS4Sd6S17S10R5A1M0A1R8S61S62S1fG0A1A5S5A3S3aS4S49S17S10R6A1A1R9S11R6A1A3S5A3S3bSe4VCST;Vrho0;VFB;VFF;R6RaS61S1fS10R7A1A1A8Se5R6S11R7A1A2A2F_;F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ftv;").
Proof using ALA HCST.
  intros tv bd am A rho tp [tr [ms md]] [Hsm (Ai & kc & HJ)] CR CX.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & _). cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
  split.
  - exact (lo_robjsR0 Ai rho _ tv _ rho tp md HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
  - exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai rho _ tv _ rho tp md HM HF HN HZ CX).
Qed.

Lemma gp_val : ltac2:(tb__ "0|0|
S15S14S12S2S16A1S81S16S18R4A1R1A3S3aS4S66S16S1bS1cR4S1aSedA1A2A1R2A3S5A3S3bS6fZ0R4A2S70R4Z1000A2A2S3aS12S36Q40S1dR7S4cR6R5A2A2A2S71S77R7R6A2R5A2A3F_;F_;F_;Ffacts;Fk;Fg;Frho;").
Proof.
  intros rho g k facts HF C Hk. pose proof (holds_mem _ _ _ HF C) as H. rewrite h_ule, uval_lit in H by (unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52; lia).
  unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52 in H. pose proof (uval_range rho g) as R.
  change (bv_unsigned (eval rho (gp g k))) with (uval rho (gp g k)). unfold gp.
  assert (Ek : uval rho (SLit k) = k) by (apply uval_lit; lia). rewrite <- Ek at 2. apply uval_add_small. rewrite Ek. lia.
Qed.
Lemma efmeas_gp : ltac2:(tb__ "0|2|
SfS24S3S12S14S12S15S3aS12S41S0S1S1SfS24A2M0S3A2S1S12S14A2S0G0S3S0SfS24R7R6A4R5A4S0S12S14R4S4cR3R2A2M1A4A4R1A2S71S72R4S73Z2Z40A2A2S36Q40S1dR1G1A2A2A2A3Frho;Fc;Fg;Fr;Fk;Fnd;FT;").
Proof. reflexivity. Qed.

Lemma X_X_fa0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4bA2Sa9R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa9S4bA4G1A4S0S12S14Z167S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD2_checks_fa as (_ & _ & _ & _ & _ & Cz & _).
  apply (TR_pre (SPA segs (JAv nd_fa) K_fa (rho_sub rho s_fa0) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc X_fa0 K_fa s_fa0 nd_fa nd_fa rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (JA_head0_none segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX tvA frL KU1 pH false X_fa0 rho tp w Cz Hw). }
  apply (CUT3 K_fa nd_fa 1%nat (250, z0) (rho_sub rho s_fa0) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_X_fa1 : ltac2:(tb__ "0|4|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S54SabSa0A2M2A2SaaR3R2A5VFAM;S41S0S1S1SfS24A2M3S3A2S1S12S14A2S0G3S3S0SfS24SaaG2A4G1A4S0S12S14Z12bS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD2_checks_fa as (_ & _ & _ & _ & _ & _ & Cz & _).
  apply (TR_pre (SPA segs (JAv nd_fa) K_fa (rho_sub rho s_fa1) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc X_fa1 K_fa s_fa1 nd_fa nd_fa rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (JA_headN_none segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX tvA frL KU1 vNx vG X_fa1 rho tp w Cz Hw). }
  apply (CUT3 K_fa nd_fa 1%nat (250, z0) (rho_sub rho s_fa1) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_X_A : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4bA2Sa7R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa7S4bA4G1A4S0S12S14Z167S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & _ & _ & CnpA & CnbA & CnpA1 & CnbA1 & CR & CX & Cnd & _).
  pose proof epiD2_checks_loop1 as (_ & _ & ClenN & CwfA1 & Cpop & CwfA2 & CbaseA1 & Chnz & _).
  apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_A2) X_A2 rho2 tp w)).
  { intros w Hw.
    destruct (JA_lenN segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX ALA HKc tvA frL KU1 pH false X_A rho tp w ltac:(rewrite ClenN; exact CwfA1) CnpA CnbA Hw) as (rho1 & _ & Hw1).
    rewrite ClenN in Hw1. fold gA in Hw1.
    destruct (JA_popN segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX ALA HCST HXGL HKc HNP tvA frL KU1 pH gA X_A1 rho1 tp w ltac:(rewrite Cpop; exact CwfA2) CbaseA1 CnpA1 CnbA1 Chnz
                ltac:(intros; exact (popN_site tvA KU1 (AHeadN pH gA) X_A1 rho1 tp w Hw1 CR CX)) Hw1) as (rho2 & _ & Hw2 & _).
    exists rho2. rewrite Cpop in Hw2. unfold nx in Cnd. rewrite Cnd in Hw2. exact Hw2. }
  apply TR_exw. intros rho2.
  apply (CUT2 X_A2 nd_A2 1%nat (350, z0) rho2 tp); [right; left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_L_L1 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S55A2Sa5R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa5S55A4G1A4S0S12S14Z15dS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_CL) C_L (rho_sub rho s_L1) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_L1 C_L s_L1 nd_A2 nd_CL rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUT2 C_L nd_CL 1%nat (300, gp vG 8) (rho_sub rho s_L1) tp); [right; right; left; reflexivity | exact I |].
  rewrite efmeas_z0, efmeas_gp. pose proof (bv_urange (eval (rho_sub rho s_L1) (gp vG 8))) as R. lia.
Qed.
Lemma X_L_L3 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S56A2Sa6R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa6S56A4G1A4S0S12S14Z12cS4cS22Sf6SacP3A2A1ZbA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & _ & C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FgL & Csub). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply TR_facts. intros HF.
  apply (TR_pre (SPA segs (JAv nd_CL) C_L (rho_sub rho s_L3) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_L3 C_L s_L3 nd_B2 nd_CL rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUT2 C_L nd_CL 1%nat (300, gp vG 8) (rho_sub rho s_L3) tp); [right; right; left; reflexivity | exact I |].
  rewrite !efmeas_gp. rewrite <- (eval_subst rho s_L3 (gp vG 8)), Csub.
  rewrite (gp_val rho (SVar (nB + 3)) 8 _ HF FgL) by lia. rewrite (gp_val rho (SVar (nB + 3)) 11 _ HF FgL) by lia.
  pose proof (uval_range rho (SVar (nB + 3))) as R. lia.
Qed.

Lemma gp_val' : ltac2:(tb__ "0|0|
S15S14S12S6fS77R3R2A2S73Z2Z34A2A2S3bS6fZ0R2A2S70R2Z1000A2A2S3aS12S36Q40S1dR5S4cR4R3A2A2A2S71S77R5R4A2R3A2A3F_;F_;Fk;Fg;Frho;").
Proof.
  intros rho g k H Hk. pose proof (uval_range rho g) as R.
  change (bv_unsigned (eval rho (gp g k))) with (uval rho (gp g k)). unfold gp.
  assert (Ek : uval rho (SLit k) = k) by (apply uval_lit; lia). rewrite <- Ek at 2. apply uval_add_small. rewrite Ek. lia.
Qed.

Lemma X_E_fd0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S57A2Sa2R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa2S57A4G1A4S0S12S14Z12cS4cSa0Z7A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD2_checks_fd as (_ & Cxf & CwfE & Cent & Cchk & Cta & Cnp & C12 & C13 & Ctidy & CwfT & _).
  pose proof epiD_chk_fd as (CdX & CR & CX & Fnz & Cpay & Cbb & Cnb & CT0 & Fg & Cgb).
  apply (TR_pre (SPA segs (JAv nd_CL) E_fd rho tp)).
  { intros w Hw. rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0)|].
    exact (SPA_axforms segs (JAv nd_CL) (xf_fd E_fd0) rho E_fd0 E_fd1 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           W2 UStopLe E_fd s_fd R_fd rho tp nd_CL 0%nat (vNd, e32 vCap) KU1 (FAM (efmeasA (E_fd0, nd_CL, 1%nat, (300, gp vG 7)) rho) tp0) CFREE
           Cent Cchk Cta Cnp Cnb Cbb eq_refl).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fd s_fd R_fd rho ((vNd, e32 vCap) :: tvA) 0%nat (vNd, e32 vCap) (KU1 ++ [BIc 0 1 KU]) (AHeadN vNx vG) eq_refl);
      [exact CR | exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. pose proof (holds_mem _ _ _ HFE Fnz) as Hd. apply (proj1 (holds_nbeq _ _ _)) in Hd.
    change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in Hd. rewrite uval_lit in Hd by lia. exact Hd.
  - intros rho' tp' Hag _. cbn [nd_tv nd_fr nd_am nd_CL ndN remove_nth]. unfold Pre_fr, L_fr in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv (ndT vNx vG)) T_fd rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT2 T_fd (ndT vNx vG) 1%nat (300, gp vG 6) rho' tp'); [right; right; right; left; reflexivity | exact I |].
    rewrite !efmeas_gp. rewrite <- (eval_agree_vals _ rho rho' (gp vG 6) Hag Cgb).
    rewrite (gp_val rho vG 6 _ HF Fg) by lia. rewrite (gp_val rho vG 7 _ HF Fg) by lia.
    pose proof (uval_range rho vG) as R. lia.
Qed.

Lemma X_X_B : ltac2:(tb__ "0|4|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S54SabSa0A2M2A2Sa8R3R2A5VFAM;S41S0S1S1SfS24A2M3S3A2S1S12S14A2S0G3S3S0SfS24Sa8G2A4G1A4S0S12S14Z12cS4cSa0Z5A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CnpB & CnbB & CRB & CXB & CndB & CnB & FgB & _ & _).
  pose proof epiD2_checks_fd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fnz & Cpop & CwfB2 & CbaseB & _).
  apply TR_facts. intros HF.
  pose proof (holds_mem _ _ _ HF FgB) as HgB. rewrite h_ule, uval_lit in HgB by (unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52; lia). unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52 in HgB.
  apply (TR_pre (fun w => exists rho2, (bv_unsigned (rw rho2 (nB + 3)%positive) + 16 = uval rho vG) /\ SPA segs (JAv nd_B2) X_B2 rho2 tp w)).
  { intros w Hw.
    destruct (JA_popN segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX ALA HCST HXGL HKc HNP tvA frL KU1 vNx vG X_B rho tp w ltac:(rewrite Cpop; exact CwfB2) CbaseB CnpB CnbB Fnz
                ltac:(intros; exact (popN_site tvA KU1 (AHeadN vNx vG) X_B rho tp w Hw CRB CXB)) Hw) as (rho2 & _ & Hw2 & Hg).
    exists rho2. unfold nx in CnB, CndB. rewrite CnB in Hg. split; [exact Hg|]. rewrite Cpop in Hw2. rewrite CndB in Hw2. exact Hw2. }
  apply TR_exw. intros rho2.
  apply (TR_pureP _ (bv_unsigned (rw rho2 (nB + 3)%positive) + 16 = uval rho vG)); [intros w [H _]; exact H|]. intros Hg.
  apply (TR_pre (SPA segs (JAv nd_B2) X_B2 rho2 tp)); [intros w [_ Hw]; exact Hw|].
  apply (CUT2 X_B2 nd_B2 1%nat (300, gp (SVar (nB + 3)) 12) rho2 tp); [right; right; right; right; left; reflexivity | exact I |].
  rewrite !efmeas_gp. rewrite (gp_val rho vG 5 _ HF FgB) by lia.
  assert (Eg : uval rho2 (SVar (nB + 3)) = bv_unsigned (rw rho2 (nB + 3)%positive)) by reflexivity.
  pose proof (uval_range rho2 (SVar (nB + 3))) as R.
  rewrite (gp_val' rho2 (SVar (nB + 3)) 12) by lia. lia.
Qed.

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1VTR;S37S23S97VAInv;R3VKc;A3S7eR2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cS7dS91VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF8 : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1VTR;S37S23S98VAInv;R3VKc;A3Sc9R2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cSc8S91VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CSF : ltac2:(tb__ "0|2|
S67S15S2S35Q40A1A1VTR;S37S23S99VAInv;Z5M0R3VKc;A4SafR2R1A5S5dS23S76R2R1S7S1SfS5cA2M1S0SfS5cSaeS95VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A2Ftp1;Frho1;FAi;").

Lemma CXR_s8a : ltac2:(tb__ "0|0|
S3aS4Sd8VXGL;S17S10Sb2A1A1S6S1S14S14A2A1Z38ZdbSb4Sb2A1A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_s8r : ltac2:(tb__ "0|0|
S3aS4Sd8VXGL;S17S10Sb3A1A1S6S1S14S14A2A1Z14Z34S11Sb3A1A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXL_sf : ltac2:(tb__ "0|0|
S3aS4Se6VXGL;S17S10Sb0A1A1S6S1S14S14A2A1S61S8S3U0A2S6S19A1Sd7S11Sb0A1A8S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma c5_ok : 0 <= 5 <= 6. Proof using . lia. Qed.
Lemma k68 : 0 <= 56. Proof using . lia. Qed.
Lemma k32 : 0 <= 20. Proof using . lia. Qed.
Lemma k68_231 : 56 <= 219 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Lemma k32_64 : 20 <= 52 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Lemma tnz_of_ule4096 : ltac2:(tb__ "0|0|
S15S2S16A1S1S14S14A2S81S16S18R3A1R2A3S3aS4S66S16S1bS1cS1aZ1000A1S9S14S14R2A3A2A1R3A3S5A3S89R5R3A2F_;F_;Ft;Ffacts;Frho;").
Proof using . intros rho facts t HF C. pose proof (holds_mem _ _ _ HF C) as Hd. rewrite h_ule, uval_lit in Hd by lia. unfold tnz. change (bv_unsigned (eval rho (fst t))) with (uval rho (fst t)). lia. Qed.
Ltac meas_z0 := rewrite !efmeas_z0; vm_compute; split; [discriminate | reflexivity].
Lemma X_sx_incl : ltac2:(tb__ "0|1|
SfS1S14S14A2M0S64G0R1Sb4R2A1A3S64G0R2S11R3A1A3F_;Fr;FE;").
Proof using . intros E r H. unfold X_sx in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma X_E_fa0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S58A2Sa1R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa1S58A4G1A4S0S12S14Zf9S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD2_checks_fa as (_ & _ & _ & _ & _ & _ & _ & _ & CwfE & Cent & Cchk & Cta & Cnp & C12 & C13 & Ctidy & CwfT & _).
  pose proof epiD_chk_fa as (CdX & CR & CX & F4096 & Cpay & Cnb & CT0).
  apply (TR_pre (SPA segs (JAv nd_fa) E_fa rho tp)).
  { intros w Hw. rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0) | exact Hw]. }
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           W2 UStopLe E_fa s_fa R_fa rho tp nd_fa 0%nat (vARn, SLit 64) [] (FAM (efmeasA (E_fa0, nd_fa, 1%nat, (249, z0)) rho) tp0) CFREE
           Cent Cchk Cta Cnp Cnb eq_refl eq_refl).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fa s_fa R_fa rho tvA 0%nat (vARn, SLit 64) KU1 ANone eq_refl); [exact CR | exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. exact (tnz_of_ule4096 rho _ (vARn, SLit 64) HFE F4096).
  - intros rho' tp' _ _. cbn [nd_tv nd_fr nd_am nd_fa tvA remove_nth]. unfold Pre_fr, L_fr in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_e) T_fa rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT3 T_fa nd_e 1%nat (240, z0) rho' tp'); [right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma efmeas_lit : ltac2:(tb__ "0|2|
SfS24S3S12S12S15S3bS6fZ0R2A2S70R2S73Z2Z40A2M0A2A2S3aS12S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24R7R6A4R5A4S0S12S14R4S1aR3A1A4A4R2A2S71S72R4G0A2R3A2A3F_;Frho;Fj;Fr;Fk;Fnd;FT;").
Proof using . intros T nd k r j rho Hj. unfold efmeasA, ef_rank, ef_var. cbn [fst snd]. change (bv_unsigned (eval rho (SLit j))) with (uval rho (SLit j)). rewrite uval_lit by lia. lia. Qed.
Lemma X_E_ml0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4bA2Sa3R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa3S4bA4G1A4S0S12S14Z167S1aZ2A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD2_checks_ml as (_ & Cxf & CentM & CchkM & _ & Cz & Czs & Czw & Cxb & Ctidy & Cwf & _).
  pose proof epiD_chk_ml as (Cta & Cnp & Cnb & Cshape & CR & CX & CT0 & Cbb).
  apply (TR_pre (SPA segs (JAv nd_d2) E_ml rho tp)).
  { intros w Hw. exact (SPA_axforms segs _ xf_ml rho E_ml0 E_ml tp w Cxf Hw). }
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_build_line_index_rom_call.purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E_ml s_ml R_ml rho tp nd_d2 KU1 (FAM (efmeasA (E_ml0, nd_d2, 1%nat, (359, SLit 2)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. exact (CMEMSET Ai rho2 tp2).
  - reflexivity.
  - reflexivity.
  - exact CentM.
  - exact CchkM.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - apply payA_same. reflexivity.
  - exact Cshape.
  - exact (site_rt_lo0 E_ml s_ml R_ml rho tvA KU1 (AHead pH false) CR CX).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_ml memset_pc s_ml R_ml rho tp tr ms md Hsm HM HX' CentM).
  - intros L rho2 tp2 [<-|[]] _ _. cbn [nd_tv nd_fr nd_am nd_d2 ndEp]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_d2) T_ml rho2 tp2)).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. apply (SPA_axforms segs _ xfb_ml rho2 T_ml1 T_ml2 tp2 w Cxb). rewrite <- Czs.
      exact (SPA_zero_cells segs _ rho2 T_ml0 1%nat z24 _ tp2 w Cz Czw Hw). }
    apply (CUT2 T_ml nd_d2 1%nat (359, SLit 1) rho2 tp2); [do 5 right; left; reflexivity | exact I | rewrite !efmeas_lit by lia; lia].
Qed.

Lemma X_E_s80 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S50A2Sa4R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa4S50A4G1A4S0S12S14Ze5S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD3_checks_s8 as (CwfA & CeqA & Cxf & Cent & Cchk & CT0 & Cxb & Cobjs & Ceq82 & Cwf82 & CeqR & CwfR & Ctidy & CwfT & _ & Czf & Czs & Czw & _).
  pose proof epiD_chk_s8 as (Cbase0 & Chf0 & CR0 & Cta & Cnp & Cnb & Cshape & CR & CX & Cbase1 & Chf1 & Cnb1 & CR1 & Cbase2 & Chf2 & CR2).
  pose proof epiD_chk_sx as (XeqA & XwfA & Xeq82 & XeqR & XwfR & _).
  apply (TR_pre (SPA segs (JAv nd_e) Ee_s8 rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv nd_e) (xf_shcall Ee_s8a 56) rho Ee_s8a Ee_s8 tp w Cxf). rewrite <- XeqA.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] frL [] ANone 0%nat 110%positive 5 120%positive g5 56 219 Ee_zf (X_sx Ee_zf) rho tp w eq_refl c5_ok Cbase0 k68
             k68_231 Chf0 (X_sx_incl Ee_zf) XwfA); [|rewrite <- Czs; exact (SPA_zero_fill segs _ rho E_s80 iOUTe _ tp w Czf Czw Hw)].
    intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    - exact (lo_robjsR0 Ai rho _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR0).
    - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ [] (X_sx Ee_zf) rho3 tp3 md3 56 219 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8a). }
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_f8 [L_f8] Ee_s8 (s_s8 Ee_s8) Re_s8 rho tp nd_e [] (FAM (efmeasA (E_s80, nd_e, 1%nat, (229, z0)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CF8.
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - reflexivity.
  - apply payA_same. reflexivity.
  - exact Cshape.
  - exact (site_rt_lo0 Ee_s8 (s_s8 Ee_s8) Re_s8 rho [] [] ANone CR CX).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am nd_e]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_e) Te_s81 rho' tp')).
    { intros w Hw. exact (SPA_axforms segs (JAv nd_e) (xf_shback Te_s80) rho' Te_s80 Te_s81 tp' w Cxb Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_e) Te_s8 rho2 tp' w)).
    { intros [tr [ms md]] Hw. exists (rho_absorb rho' [shobj g5 56 219 [] DUnknown] (vms md tp' ms)).
      rewrite <- Ctidy. apply SPA_tidy. rewrite <- XeqR.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               [] frL [] ANone 0%nat 110%positive 5 120%positive g5 20 52 Te_s82 (ax_X Te_s82) _ tp' (tr, mkCfg ms md) eq_refl c5_ok Cbase2 k32
               k32_64 Chf2 (fun r H => H) XwfR).
      - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
        + exact (lo_robjsR0 Ai _ _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR2).
        + exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai _ _ [] (ax_X Te_s82) rho3 tp3 md3 20 52 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8r).
      - rewrite <- Xeq82.
        apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
                 [] frL [] ANone 0%nat 110%positive 5 120%positive g5 56 219 [] DUnknown Te_s81 (objs_butlast Te_s81) [] rho' tp' tr ms md
                 eq_refl c5_ok Cbase1 Cobjs k68 k68_231 eq_refl Chf1 eq_refl Cnb1); [|exact Hw].
        intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (lo_robjsR0 Ai rho' _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR1). }
    apply TR_exw. intros rho2.
    apply (CUT3 Te_s8 nd_e 1%nat (220, z0) rho2 tp'); [right; right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma site_sf : ltac2:(tb__ "0|8|
SfS87S2S19A1S15S3aS4Sf5S17S10R4A1A1S6S1S14S14A2A1M0S61S8S3U0M1A2M2S62R2A6S5A3S3aS4Se6VXGL;S17S10R5A1A1G0S61G2S6S19A1Sd7S11R5A1A8S5A3S3aS14S84R5PcM3A2S7fA3S3aS14S84R6S9aA2S80A3S67S81S16S18R6A1S17S10R9A1A1A3VP0;Vrho0;A1Sb5S7cVrho0;R8A3S2dVFB;R4A2S2eVFF;R5A2S2aVFB;R6RbG0A4S8aRcG0A2S8dRdG0A2S29VFF;R9ReS61A4S3cS15S15S3cS2S35Q40A1A1M4G4S3cS74S74VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S28Vrho0;RbA2S8bR11S69S68RcA1A1A2S3bSdeVCST;Vrho0;VFB;VFF;R12G0S88S1S1S14S12A2M5S14A2G1S61A3M6R13A8S3bSe0VCST;VXGL;Vrho0;VFB;VFF;R12G0G6S11R15A1A9S3bS3aS12S77R12S84R14G3A2A2S77R12S9S14S12S9G5S14S0G5S14S0S14S12S7fZ5A4S80A4M7A3A3A2A3S3aS12S77R12S84R14S9aA2A2S77R12ScG5S14G7A3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;F_;F_;F_;F_;Frho;FR;Fs;FE;").
Proof using ALA HXlits.
  intros E s R rho HR HX Hs12 Hs16 Ai HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split; [|rewrite Hs12, Hs16; cbn [fst snd]; split; reflexivity]].
  - intros o a Ho Hr.
    apply (TobjJAT.robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [] frL (Some 0%nat) extraLO R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HR) with (o := o); [| exact Ho | exact Hr].
    intros o' a' _ HE Hr'. exact (extraLO_pclMA CST rho0 FB FF rho [] _ o' a' Hav HP0 HE Hr').
  - apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho _ [] frL (Some 0%nat) [] extraXlo (ax_X E) rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HX).
    intros r' a' _ HE Ha. unfold extraXlo in HE. apply lazy_orb_prop in HE as [HE|HE].
    + left. exact (xextraLO_pclMA CST rho0 FB FF rho [] _ r' a' Hav HP0 HE Ha).
    + right. apply HXlits. exact (xr_inlits_sound r' rho a' HE Ha).
Qed.

Lemma X_Ee_sf0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S50A2Sb1R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sb1S50A4G1A4S0S12S14ZdbS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD3_checks_sf as (CxfA & CwfB & CxfC & CxfD & CwfE & Cent & Cchk & CwfT & _).
  pose proof epiD_chk_sf as (CbaseA & CobjsA & Cdw & ChfA & CnbA & CRA & CeqB & CbaseD & CeqF & CswfF & CRD & CXD & Cta & Cnp & Cnb & C12 & C16 & CRsf & CT0 & Ctidy).
  pose proof epiD_chk_sx as (_ & _ & _ & _ & _ & XeqB & XwfF).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_e) Ee_sf rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 20 52 (ob_cells she) (ob_dflt she)] (vms md tp ms)).
    rewrite <- CeqF.
    apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] frL [] ANone 0%nat 110%positive 5 120%positive Ee_sfD _ tp (tr, mkCfg ms md) eq_refl c5_ok CbaseD XwfF).
    - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      + intros o a Ho Hr. destruct (lo_robjsR0 Ai _ _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRD o a Ho Hr) as [X|X]; [left; exact X | right; left; exact X].
      + exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai _ _ [] _ rho3 tp3 md3 HM HF HN HZ CXD).
    - apply (SPA_axforms segs (JAv nd_e) (xf_merge Ee_sfC) _ Ee_sfC Ee_sfD tp _ CxfD).
      apply (SPA_axforms segs (JAv nd_e) (xf_rebase Ee_sfB) _ Ee_sfB Ee_sfC tp _ CxfC).
      rewrite <- XeqB.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               [] frL [] ANone 0%nat 110%positive 5 120%positive g5 20 52 (ob_cells she) (ob_dflt she) Ee_sfA (objs_butlast Ee_sfA) [] rho tp tr ms md
               eq_refl c5_ok CbaseA CobjsA k32 k32_64 Cdw ChfA eq_refl CnbA).
      + intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (lo_robjsR0 Ai rho _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRA).
      + exact (SPA_axforms segs (JAv nd_e) (xf_sh Ee_sf0) rho Ee_sf0 Ee_sfA tp _ CxfA Hw). }
  apply TR_exw. intros rho1.
  unfold Pre_sf, L_sf in Cent, Cchk.
  apply (sfree_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           5 Ee_sf (s_sf Ee_sf) Re_sf (ax_X Ee_sf) rho1 tp nd_e 0%nat (vF, 5, vFL) (FAM (efmeasA (Ee_sf0, nd_e, 1%nat, (219, z0)) rho) tp0) CSF c5_ok).
  - intros r H. exact H.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A A' _. exact I.
  - exact (site_sf Ee_sf (s_sf Ee_sf) Re_sf rho1 CRsf CXL_sf C12 C16).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_bd nd_am nd_e remove_nth frL]. unfold Pre_sf, L_sf in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_z) Te_sf rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT3 Te_sf nd_z 1%nat (210, z0) rho' tp'); [right; right; right; left; reflexivity | exact I | meas_z0].
Qed.

Hypothesis XOK : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAv;S4bA1S9fR3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24S9fS4bA4U1A4S0S12S14Z167S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Hypothesis XPOST : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAv;S4fA1SadR3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24SadS4fA4U1A4S0S12S14Zd1S6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").

Lemma exitsD1_ok : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S59A3VTR;S37S23VJAFv;S42S4aR6A2R7A2R8R4R3A5VFAM;S41S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsD1 In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <- <- <-.
  - apply X_E_bd0.
  - apply X_L_j1s.
  - apply X_L_fl. exact (proj1 epiD_chk_fl).
  - apply X_L_fl. exact (proj1 (proj2 epiD_chk_fl)).
  - apply X_Lb_j1.
Qed.
Lemma exitsD2_ok : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S5aA3VTR;S37S23VJAFv;S42S4aR6A2R7A2R8R4R3A5VFAM;S41S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsD2 In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; injection E as <- <- <- <-.
  - apply TR_JAF. intros _. apply XOK.
  - apply X_X_fa0.
  - apply X_X_A.
  - apply X_L_L1.
  - apply X_E_fd0.
  - apply X_X_fa1.
  - apply X_X_B.
  - apply X_L_L3.
  - apply X_E_ml0.
Qed.
Lemma exitsD3_ok : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S5bA3VTR;S37S23VJAFv;S42S4aR6A2R7A2R8R4R3A5VFAM;S41S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsD3 In] in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-.
  - apply X_E_fa0.
  - apply X_E_s80.
  - apply X_Ee_sf0.
  - apply TR_JAF. intros _. apply XPOST.
Qed.
End X.

Lemma HamPD_bd : ltac2:(tb__ "0|0|
S81SdbSdbS3aS27S33ScSfS24R1A3A1S32A3Ld;Sc2A3"). Proof. repeat constructor. Qed.
Lemma P0_bd_mono : ltac2:(tb__ "0|2|
S2S1S12S12A2M0A1M1G1S2S1G0S12A2A1S15G0S64G0R1R5A3S64G0R2R5A3F_;Fbn;S83R5R3R2A3S83R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S34S23VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S9bS23S92VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S12S64S12R1S7S12Z0S7S12Zf5S7S12Zf8S6S12A1A3A3A3A3Se9S23S92VAInv;VCST;VXGL;R2A6F_;Fxx;").
Variable FAMQ : list word -> assn.

Hypothesis XOK_T : ltac2:(tb__ "0|1|
S15S2S35Q40A1A1M0G0S6cS23Vok;S37S23VJAv;S4bA1S9fR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XPOST_T : ltac2:(tb__ "0|1|
S15S2S35Q40A1A1M0G0S6cS23Vok;S37S23VJAv;S4fA1SadR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CBD_T : ltac2:(tb__ "0|1|
S2S1S12S12A2M0A1S2S1G0S12A2A1S7aS15S2S35Q40A1A1S79Z5R3A2S6cS23Vok;S37S23S2cVAInv;VCST;VXGL;VKc;S83R6R5A2R6R5R4S25Sd3ScfSbSd2U0A1A3AaSd1R3R2A5S5dS23Sd0R3R2Sd4VAInv;VCST;VXGL;VKc;S83S25SbaR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_bd.
  eapply (sum_PostsC_k segs AInv CST XGL Kc BDP.P0_bd PTrue BD.Pre_bd (ndh h0 false (BD.ndL 0)) (PDh PD_bd h0 false) BD.NP); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc BDP.P0_bd PTrue BD.Pre_bd (BD.ndL 0) PD_bd BD.NP h0 false h0_ltBD eq_refl HamPD_bd P0_bd_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 _.
  exact (BDP.builder_dispose_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' rho3 ok' Hok' AC tp3).
Qed.
Lemma CFREE_T : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1S6cS23Vok;S37S23S96VAInv;Sc7S93R3VKc;A5SbbR2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cSb9S94VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [right; right; left; reflexivity | exact HKc | exact (proj1 Hok) | exact (proj2 Hok)]. Qed.
Lemma CMEMSET_T : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1S6cS23Vok;S37S23S97VAInv;R3VKc;A3S7eR2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cS7dS91VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CF8_T : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1S6cS23Vok;S37S23S98VAInv;R3VKc;A3Sc9R2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cSc8S91VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSC 248 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CSF_T : ltac2:(tb__ "0|2|
S67S15S2S35Q40A1A1S6cS23Vok;S37S23S99VAInv;Z5M0R3VKc;A4SafR2R1A5S5dS23S76R2R1S7S1SfS5cA2M1S0SfS5cSaeS95VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_stack_free _ _ _ _ _ AC 5 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.

Let famS (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6eS3eSf2S23S82S44Sf0S48VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBX;S25S4aAcS82S43S44S46Vcuts;A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|6|
S2S1S1S1SfS24A2M0S3A2M1S1S12S14A2M2A2M3A1S2S35Q40A1A1M4SfS24S3G2S15G4S12G4S64G3S0G1G2S0G0S3S0SfS24R8R7A4R6A4R5A4RaA3S42S4aR7R5A3S3bS6fZ0S41S0G1G2S0G0S3S0SfS24RaR9A4R8A4R7A4R6A2M5A2S70G5R4A2A2S6cS23Vok;S37S23VJAv;RaA1RbR7R6A5VfamS;RdRcR5R4A4A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD ok (map efdrop cuts) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S2S43A1S2S35Q40A1A1M0S6dS12G0S6cS23Vok;R3VFAMQ;R4A1A4S6cS23Vok;R4VfamS;R6R5R3R2A4A4F_;Ftp0';Fb;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma D3_T : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S53A3S42S4aR6R4A3S6cS23Vok;S37S23VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD3_ok FUEL_oz cps_ad NP cutsD3 exitsD3 ok (FAMQ tp0) Hok
           ecertD3_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsD3_ok (triple segs ok) (famS cutsD3 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CFREE_T (reenterS cutsD3 tp0) CF8_T CSF_T
           (fun rho tp tp0' => rightS cutsD3 tp0 _ _ tp0' (XPOST_T rho tp tp0)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma D2_T : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S52A3S42S4aR6R4A3S6cS23Vok;S37S23VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD2_ok 300%nat cps_ad NP cutsD2 exitsD2 ok (FAMQ tp0) Hok
           ecertD2_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsD2_ok (triple segs ok) (famS cutsD2 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CFREE_T (reenterS cutsD2 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsD2 tp0 _ b tp0' (D3_T T nd k rv rho tp tp0 Hi Hp)) CMEMSET_T
           (fun rho tp tp0' => rightS cutsD2 tp0 _ _ tp0' (XOK_T rho tp tp0)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma D1_T : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S51A3S42S4aR6R4A3S6cS23Vok;S37S23VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD1_ok 300%nat cps_ad NP cutsD1 exitsD1 ok (FAMQ tp0) Hok
           ecertD1_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsD1_ok (triple segs ok) (famS cutsD1 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CBD_T CFREE_T (reenterS cutsD1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsD1 tp0 _ b tp0' (D2_T T nd k rv rho tp tp0 Hi Hp)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiD_T : ltac2:(tb__ "0|1|
S15S2S35Q40A1A1M0G0S63R3A1S6cS23Vok;S37S23VJAv;S4eA1Sb8R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (D1_T K_disp nd_d0 0%nat (390, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S9cS23S92VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S12S64S12R1S7S12Z0S7S12Zf5S7S12Zf8S6S12A1A3A3A3A3SeaS23S92VAInv;VCST;VXGL;R2A6F_;Fxx;").
Variable FAM : ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6dF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S12S12S2S35Q40A1A1S6eS6fR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XOK_E : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0S6bS23S37S23VJAv;S4bA1S9fR3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24S9fS4bA4U1A4S0S12S14Z167S6aA4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XPOST_E : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0S6bS23S37S23VJAv;S4fA1SadR3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24SadS4fA4U1A4S0S12S14Zd1S6aA4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CBD_E : ltac2:(tb__ "0|1|
S2S1S12S12A2M0A1S2S1G0S12A2A1S7aS15S2S35Q40A1A1S79Z5R3A2S6bS23S37S23S2cVAInv;VCST;VXGL;VKc;S83R6R5A2R6R5R4S25Sd3ScfSbSd2U0A1A3AaSd1R3R2A5S5dS23Sd0R3R2Sd4VAInv;VCST;VXGL;VKc;S83S25SbaR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_bd.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc BDP.P0_bd PTrue BD.Pre_bd (ndh h0 false (BD.ndL 0)) (PDh PD_bd h0 false) BD.NP); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc BDP.P0_bd PTrue BD.Pre_bd (BD.ndL 0) PD_bd BD.NP h0 false h0_ltBD eq_refl HamPD_bd P0_bd_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 _.
  exact (BDP.builder_dispose_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' rho3 ACX tp3).
Qed.
Lemma CFREE_E : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1S6bS23S37S23S96VAInv;Sc7S93R3VKc;A5SbbR2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cSb9S94VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [right; right; left; reflexivity | exact HKc]. Qed.
Lemma CMEMSET_E : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1S6bS23S37S23S97VAInv;R3VKc;A3S7eR2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cS7dS91VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc. Qed.
Lemma CF8_E : ltac2:(tb__ "0|1|
S67S15S2S35Q40A1A1S6bS23S37S23S98VAInv;R3VKc;A3Sc9R2R1A5S5dS23S76R2R1S7S1SfS5cA2M0S0SfS5cSc8S91VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSCX 248 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma CSF_E : ltac2:(tb__ "0|2|
S67S15S2S35Q40A1A1S6bS23S37S23S99VAInv;Z5M0R3VKc;A4SafR2R1A5S5dS23S76R2R1S7S1SfS5cA2M1S0SfS5cSaeS95VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_stack_free _ _ _ _ _ ACX 5 ltac:(cbn; tauto)). exact HKc. Qed.

Let famE (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6eS3eSf1S23S82S43SefS47VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBX;S25S4aAcVcuts;A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|6|
S2S1S1S1SfS24A2M0S3A2M1S1S12S14A2M2A2M3A1S2S35Q40A1A1M4SfS24S3G2S15G4S12G4S64G3S0G1G2S0G0S3S0SfS24R8R7A4R6A4R5A4RaA3S42S4aR7R5A3S3bS6fZ0S41S0G1G2S0G0S3S0SfS24RaR9A4R8A4R7A4R6A2M5A2S70G5R4A2A2S6bS23S37S23VJAv;RaA1RbR7R6A5VfamE;RdRcR5R4A4A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD cuts T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S2S43A1S2S35Q40A1A1M0S6dS12S12G0S6fR3R2A2S6bS23R5VFAM;R4R6A2A3S6bS23R6VfamE;R8R7R4R3A4A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma D3_E : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S53A3S42S4aR6R4A3S6bS23S37S23VJAv;R8A1R9R5R4A5VFAM;S41S0G3G0S0G2S3S0SfS24R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD3_ok FUEL_oz cps_ad NP cutsD3 exitsD3 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertD3_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsD3_ok (etriple segs) (famE cutsD3 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CFREE_E (reenterE cutsD3 tp0) CF8_E CSF_E
           (fun rho tp tp0' => rightE cutsD3 tp0 _ _ _ tp0' (Z.le_refl _) (XPOST_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma D2_E : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S52A3S42S4aR6R4A3S6bS23S37S23VJAv;R8A1R9R5R4A5VFAM;S41S0G3G0S0G2S3S0SfS24R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD2_ok 300%nat cps_ad NP cutsD2 exitsD2 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertD2_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsD2_ok (etriple segs) (famE cutsD2 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CFREE_E (reenterE cutsD2 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsD2 tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (D3_E T nd k rv rho tp tp0 Hi Hp)) CMEMSET_E
           (fun rho tp tp0' => rightE cutsD2 tp0 _ _ _ tp0' (Z.le_refl _) (XOK_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma D1_E : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S64S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S51A3S42S4aR6R4A3S6bS23S37S23VJAv;R8A1R9R5R4A5VFAM;S41S0G3G0S0G2S3S0SfS24R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD1_ok 300%nat cps_ad NP cutsD1 exitsD1 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertD1_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsD1_ok (etriple segs) (famE cutsD1 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CBD_E CFREE_E (reenterE cutsD1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsD1 tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (D2_E T nd k rv rho tp tp0 Hi Hp)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem epiD_E : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0S63R3A1S6bS23S37S23VJAv;S4eA1Sb8R4R3A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24Sb8S4eA4U0A4S0S12S14Z186S6aA4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (D1_E K_disp nd_d0 0%nat (390, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Existence.
End Sum.
