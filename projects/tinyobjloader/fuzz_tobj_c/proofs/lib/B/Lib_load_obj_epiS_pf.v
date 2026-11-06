(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "nat"; "list"; "true"; "bool"; "app"; "Some"; "cons"; "nil"; "option"; "false"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "AHead"; "NDA"; "nd_below"; "JA"; "TPA"; "fbinA"; "ffinA"; "frinA"; "frozen"; "ok_frameKA"; "tvinA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "ss_next"; "ss_facts"; "sprop_eqb"; "holds"; "sprop_below"; "sobj"; "agree_below"; "SLit"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "PhisS"; "ldefR"; "V_ldR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "phiK"; "efmeasA"; "efnode"; "wsub_id_on"; "fnode"; "JAF"; "bud_le2"; "efdrop"; "enodeIAF"; "nodeIAF"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_eqs"; "RB"; "zl"; "cutsS1"; "cutsS2a"; "cutsS2b"; "cutsS4"; "ndZ"; "exitsS1"; "exitsS2a"; "exitsS2b"; "exitsS4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "add"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "nd_succ"; "kept_fs2"; "nd_s0"; "PDk_fs2"; "Es_fs0"; "L_dz"; "L_sk"; "L_sn"; "R_fs2"; "bd_succ"; "nd_fz2"; "nd_nop2"; "nd_ok2"; "E_fs2"; "E_fs21"; "Xk_fs2"; "bd_s0"; "nnPhi"; "passed_fs2"; "s_fs2"; "tv_fs2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "ndAt"; "K_rp"; "nd_rp"; "L_cf0"; "bnds"; "L_w"; "wK2"; "B_1"; "LR"; "PDk_vf"; "PreR"; "wK1"; "E_wm0"; "L_rpx"; "bd_succP"; "ent_chk2"; "nd_succP"; "ENDOWs"; "kept_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_chk"; "Fx"; "nx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "entails_frA"; "call_checkA"; "import_postA"; "J_ofPA"; "call_checkPA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_pf.FU"; "Pre_fu"; "Posts_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "ldef"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1.FSP"; "P0_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_pf.VFP"; "P0_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "bitem"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "K_disp"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_pure"; "J_pure_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1.FS"; "NP"; "Pre_fs"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS4"; "nd_d0"; "E0_8"; "E_fu0"; "L_d6f"; "L_d6y"; "L_d6z"; "L_d7"; "L_land"; "land_chk"; "nd8"; "nd9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_chk"; "cc_facts"; "f_len"; "f_nx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_pf.VF"; "Pre_vf"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "white_lo"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "V_ld"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS3"; "E0_1"; "E0_2"; "E0_3"; "E0_4"; "E0_5"; "E0_6"; "L_d1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3 Lib_load_obj_epiD_eqs Lib_load_obj_epiD_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiS1 Lib_load_obj_epiS_kit Lib_load_obj_epiS2 Lib_load_obj_epiS3 Lib_load_obj_epiS4 Lib_load_obj_epiS_defs Lib_load_obj_epiS_blk
  Lib_load_obj_epiS_st1 Lib_load_obj_epiS_st2 Lib_load_obj_epiS_st3 Lib_load_obj_epiS_eqs Lib_load_obj_epiS_eqs2 Lib_load_obj_epiS_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_epiD_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DP. Include Lib_load_obj_epiD_pf. End DP.
Module FU. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_unknowns. End FU.
Module VF. Include Lib_vec_finalize. End VF. Module VFP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf. End VFP.

Lemma efmeas_lit : ltac2:(tb__ "0|2|
SdS13S2S21S21S23S34S57Z0R2A2S58R2S5aZ2Z40A2M0A2A2S33S21S3bS0S1S1SdS13A2M1S2A2S1S21S24A2S0G1S2S0SdS13R7R6A4R5A4S0S21S24R4S48R3A1A4A4R2A2S5bS59R4G0A2R3A2A3F_;Frho;Fm;Fr;Fk;Fnd;FT;").
Proof. intros T nd k r m rho Hm. unfold efmeasA. cbn [ef_rank ef_var fst snd]. pose proof (uval_lit rho m Hm) as E. unfold uval in E. unfold zl. rewrite E. reflexivity. Qed.
Lemma lines_in_kept_fs2 : ltac2:(tb__ "0|0|
S44S1S24S24A2S0S24S24Sc8Se2Z10Sc9A2A4S5eA3").
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_tvL : ltac2:(tb__ "0|0|
S44S1S24S24A2S0S24S24Sc8Sa2A4S93A3").
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma c5_ok : 0 <= 5 <= 6. Proof. lia. Qed.
Lemma kw1 : 0 <= wK1. Proof. unfold wK1. lia. Qed.
Lemma kw12 : ltac2:(tb__ "0|0|
S34S57S7dS78A2S57S78S5cSe1Z5A1Z8A2A2A2"). Proof. unfold wK1, wK2. change (fs_frame_size 5) with 2048. lia. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sa6S23S3S2eQ40A1A1S8eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sb0S12VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S21ScdVCST;R1A2S34S57Z0R2A2S58R2Se0A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S21ScdVXGL;R1A2S34S57Z0R2A2S58R2Se0A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S21Se4R1A1ScdVXGL;R2A2F_;Fa;").
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1S21S21A2S21A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S23OFr;") := ltac2:(tb__ "0|0|
Se5VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S19VAInv;VCST;VXGL;S52VKc;Vrho0;VP0;VFB;VFF;VBX;S14Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3fVAInv;VCST;VXGL;S52VKc;Vrho0;VP0;VFB;VFF;VBX;S14VPhi;Vnd;Ad").

Lemma nnPhi2_holds : ltac2:(tb__ "0|0|
S23S3S2eQ40A1A1S3S8fA1S8eS96S25S29R4A1S27SeS6bA1A1A3VJAv;S17S71S92S6dS16Sc7S4A2A4R5R4R3R2A5S29R6S6eA2F_;F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md HF (Ai & kc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBU & _).
  cbn [nd_bd] in HBU. destruct HBU as (_ & _ & _ & _ & _ & _ & Hnn & _).
  pose proof epiS_chk_fs as (_ & _ & _ & _ & _ & _ & _ & C14 & F1c & F2c & F3c & _).
  assert (Hin : In (nth 14 bd_s0 (BIc 0 0 0)) bd_s0) by (apply (nth_error_In _ 14); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (Forall_forall _ _) Hnn _ Hin) as N0. rewrite C14 in N0.
  unfold PHIe in N0. cbv beta iota delta [bival lfval aval bi_f bi_c] in N0.
  pose proof (holds_mem _ _ _ HF F1c) as F1. pose proof (holds_mem _ _ _ HF F2c) as F2. pose proof (holds_mem _ _ _ HF F3c) as F3.
  rewrite h_ule in F1, F2, F3. rewrite uval_lit in F1, F3 by lia.
  pose proof (uval_range rho (t_c (v_sh vsP))) as Rc. pose proof (uval_range rho (kb 128 (t_k (v_sh vsP)))) as Rk.
  assert (Ec : uval rho (kb 128 (t_c (v_sh vsP))) = 128 * uval rho (t_c (v_sh vsP))) by (unfold kb; apply uval_mul_lit; lia).
  rewrite uval_lit in N0 by lia.
  unfold nnPhi. rewrite h_ule.
  rewrite (uval_mul_lit rho 4 (kb 128 (t_k (v_sh vsP)))) by lia.
  rewrite uval_add_small; rewrite ?uval_lit by lia; rewrite ?(uval_mul_lit rho 6 (kb 128 (t_c (v_sh vsP)))) by lia; lia.
Qed.

Lemma HIN_fs2 : ltac2:(tb__ "0|1|
S23Sa9Sa6S23S3S2eQ40A1A1S8eS96S25S29R6A1S27SeS6aA1A1A3VP0;Vrho0;A1SdcS52Vrho0;R8A3VAInv;R7R6R5R4A4S1aVrho0;R8A2Se8RbSa8Sa7R9A1A1A2S1bVFB;RaA2S1cVFF;RbA2S20VFB;RcReS6S1S24S24A2S5eS6fA3M0A4Se9RfG0A2SeaR10G0A2S1dVFF;RfR11S92A4S34Sf0VCST;Vrho0;VFB;VFF;R12S5eS92S65A8S34Sf1VCST;VXGL;Vrho0;VFB;VFF;R12S5eS92S6cA9S98Se7VFB;R12S5eA3SefVFF;R12S92A3Sa4Sa3R12S65R11A3S70A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof epiS_chk_fs as (CR & CX & CvF & _ & _ & Cs12 & Cs100 & _).
  assert (HNk : tvinA FB Ai rho kept_fs2) by (apply (tvinA_sublist FB Ai rho (kept_fs2 ++ passed_fs2)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_fs2) by (exact (tvd_app_l rho kept_fs2 passed_fs2 HD)).
  assert (HZk : tvz rho kept_fs2) by (apply (tvz_sublist rho (kept_fs2 ++ passed_fs2)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (DP.lo_robjsF0 AInv CST ALA HCST FB FF rho0 Ai rho _ kept_fs2 R_fs2 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_fs2 Xk_fs2 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold FSP.P0_fs. rewrite !rw_call', Cs12, Cs100.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    pose proof (holds_mem _ _ _ HF CvF) as HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E448 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E368 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E448; apply uval_add_small; rewrite E448; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E368; apply uval_add_small; rewrite E368; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S3S25A1S3S9eA1S33S5S9fR1A1S4A3Sf2S52Vrho0;VP0;R3S2dZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using . intros facts bd Hw. exact (DP.payA_same CST FB FF rho0 facts bd Hw). Qed.

Lemma CXR_w : ltac2:(tb__ "0|0|
S33S5SdbVXGL;S27SeS77A1A1S93S7dS78S11S77A1A6S4A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_rp : ltac2:(tb__ "0|0|
S33S5SdbVXGL;S27SeS73A1A1S93S7dS78S11S79A1A6S4A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S21S3S2eQ40A1A1S53F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S30SdS23S3S2eQ40A1A1S53S96S25S29R3A1S27SeR4A1A1A3VTR;S2fS12R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S53S53S53S56R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S53OS53S56R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S30S30SdSdSa5S3S2bA1M0S3S1SdS88A2M1A1S3S1S24S24A2M2A1S53S23S3S2eQ40A1A1M3G2S44G2R1R5A3S44G2R2S11RbA1A3F_;Fr;S33SaG0A1S89RaR9R8A3S7G0R7A2A3S33S5S8dRbRaR9R8S95G1SdScSdS88A2R7A4A5S4A3S23G3VTR;S2fS12RfRdR2R1A5S87S12S26SeRdA1A1R2R1RaA5A2Ftp1;Frho1;S3S8fA1M4Sa9S8eS31S12R9R8R10S0G4Sb1R3Sb2R2R1A2A4A5R13RaR9R4R2A4R13Sa4Sa3RbRfS9aR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SdS88G4Sa9S8eS23G3G4Sa9S8eS44G1S0SdS88RaR9A4R14A3S31S12R12R11R19S0G4Sb1R9Sb2R8R7A2A4A5R1cR13R12RaR8A4SdcS26SeR1aA1A1Sa4Sa3R14R18S9aR9R13RaA3A3R19A2R8A3S31S12R9R8ReS0G4Sb1R7Sb2R6R5A2A4A5ReSa4Sa3R16R1aS9aRbR15RcA3A3R1bA2R15RaR9R8R6A6S34SedR17S9aRcR16RdA3R1bR1cR1dR10R1eR19RbA9S23SddR18S9aRdR17ReA3R1cR1dSeR1eA1SeR1fA1SeR11A1R1RcA9VTR;S2fS12S8cR11Sa4Sa3R19R1dS9aReR18RfA3A3R1eA2R18RdRcA5SeeR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2fS12R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S23OF_;S13SdS23S3S2eQ40A1A1S53R6R3A1VTR;S2fS12VJAv;R6A1R5R4R3A5R2A2F_;VTR;S2fS12VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CHF : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S9dS23S3S2eQ40A1A1S9cZ5R3A2VTR;S2fS12S15VAInv;VCST;VXGL;VKc;S98R6R5A2R6R5R4S14Sb5AaSb4R3R2A5S87S12Sb3R3R2Sa0VAInv;VCST;VXGL;VKc;S98S14S60R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CVF : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S9dS23S3S2eQ40A1A1S9cZ4R3A2VTR;S2fS12S15VAInv;VCST;VXGL;VKc;S99VCST;R6R5A3R6R5R4S14Sc5AaSc4R3R2A5S87S12S9bR3R2Sa0VAInv;VCST;VXGL;VKc;S99VCST;A1S14S7bR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis PURE_fu : ltac2:(tb__ "0|2|
SdSa5S3S2bA1M0S23S3S2eQ40A1A1S13S53S33SaG0A1S89R7S90R6A3S7G0R5A2A3S33S5S8aR8S90R7R6S95SfSdS10S91A4A5S4A3S33S5SceS52S26SeR9A1A1A2S4A3S33S5S18S26SeRaA1A1R5A2S4A3S33S5S46S25S2aS26SeRbA1M1A1A1S27G1A1A3S4A3SfS23S44SfR2S91A3S2cS26SeRfA1A1RcR2A3VTR;S2fS12VJAv;RbA1ScaS27SeR10A1A1S8bRfS90S10R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S2fS12VJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CMEMCPYR : ltac2:(tb__ "0|2|
Sa6S23S3S2eQ40A1A1M0VTR;S2fS12S23G0S3S8fA1S8eS34SadVAInv;R7VKc;R4R3R2R1A7S35A2Lm;Lt;Lp;Lr;S7cR2R1A5S87S12S9bR2R1S8S1SdS88A2M1S0SdS88S7aSacVAInv;VCST;VXGL;R3VKc;A5A4S9G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CUTS1 : ltac2:(tb__ "0|5|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1S21G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4S49A3S3aS37R7R5A3S34S57Z0S3bS0G3G0S0G2S2S0SdS13RaR9A4R8A4R7A4R6A2M4A2S58G4R4A2A2VTR;S2fS12VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUTS2a : ltac2:(tb__ "0|5|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1S21G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4S4aA3S3aS37R7R5A3S34S57Z0S3bS0G3G0S0G2S2S0SdS13RaR9A4R8A4R7A4R6A2M4A2S58G4R4A2A2VTR;S2fS12VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUTS2b : ltac2:(tb__ "0|5|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1S21G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4S4bA3S3aS37R7R5A3S34S57Z0S3bS0G3G0S0G2S2S0SdS13RaR9A4R8A4R7A4R6A2M4A2S58G4R4A2A2VTR;S2fS12VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUTS4 : ltac2:(tb__ "0|5|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1S21G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4S4cA3S3aS37R7R5A3S34S57Z0S3bS0G3G0S0G2S2S0SdS13RaR9A4R8A4R7A4R6A2M4A2S58G4R4A2A2VTR;S2fS12VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis KDISP : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0S21G0S94R4A1S58S59Z186S5aZ2Z40A2A2R3A2VTR;S2fS12VJAv;Sb6A1Sa1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;").
Hypothesis CONT_cf : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S5dA2S75R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S75S5dA4G1A4S0S21S24Z18aS97A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Hypothesis RP : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0S21G0S38R4A1S57S5bS59S47S5aZ2Z40A2A2Z37fA2R3A2VTR;S2fS12VJAv;S74A1S73R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;").

Ltac meas := rewrite ?DP.efmeas_z0, ?efmeas_lit by (vm_compute; split; [discriminate | reflexivity]); vm_compute; split; [discriminate | reflexivity].

Lemma X_LANDf : ltac2:(tb__ "0|1|
SdS3S9eA1S24S21S23S3S2eQ40A1A1M0G0S33S5SbeR7R6R5A3S4A3S33S5S3dSd3SaaS52SeR8A1SeSa1A1A3A2S4A3S58S59Z186S5aZ2Z40A2A2R6A2S38R6A1VTR;S2fS12VJAv;S17S93S92RaS16R9SbA2A4A1RbR7R6A5VFAM;R8R5A2A2F_;F_;F_;F_;Ftp0;Ftp;Frho;Fb;Fhd;Fbd;FL;").
Proof.
  intros L bd hd b rho tp tp0 HC HP Hb HPHI.
  destruct (land_chk_unf L bd hd HC) as (P1 & P2 & PPay & HE).
  destruct (ent_chk2_unf L K_disp _ nd_d0 HE) as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply TR_facts. intros HF.
  apply (TR_pre (SPA segs (JAv nd_d0) K_disp (rho_sub rho (infer_sub NP (ax_S L) (ax_S K_disp))) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L K_disp _ (NDA tvL frL (bd_land bd) (AHead hd false)) nd_d0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL (AHead hd false) bd (comOf bd) (ekOf bd) bd_disp (bd_land bd) _ L rho tp w P1 P2 HF PPay Hw). }
  apply KDISP; [|exact Hb].
  exact (phi_sub V_ld ldef ldef_reads _ rho HP (ldefR_ldef rho HPHI)).
Qed.
Lemma X_LANDt : ltac2:(tb__ "0|1|
SdS3S9eA1S24S21S23S3S2eQ40A1A1M0G0S33S5SbeR7R6R5A3S4A3S33S5S3dSd3SaaS52SeR8A1SeSa1A1A3A2S4A3S58S59Z186S5aZ2Z40A2A2R6A2S38R6A1VTR;S2fS12VJAv;S17S93S92RaS16R9S4A2A4A1RbR7R6A5VFAM;R8R5A2A2F_;F_;F_;F_;Ftp0;Ftp;Frho;Fb;Fhd;Fbd;FL;").
Proof.
  intros L bd hd b rho tp tp0 HC HP Hb HPHI.
  apply (TR_pre (SPA segs (JAv (NDA tvL frL bd (AHead hd false))) L rho tp)); [|exact (X_LANDf L bd hd b rho tp tp0 HC HP Hb HPHI)].
  intros w Hw. apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX). exact Hw.
Qed.

Lemma X_Es_fs0 : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S5fA2S61R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S61S5fA4G1A4S0S21S24Z18eS97A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS1_checks_fs as (_ & Cxf & Cfeq & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp).
  pose proof epiS_chk_fs as (_ & _ & _ & CLF & C500 & _ & _ & _ & _ & _ & _ & Chand).
  set (ndv := NDA tv_fs2 frL bd_s0 (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_fs2 rho tp)).
  { intros w Hw. rewrite <- Cfeq. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_fs2 rho Es_fs0 E_fs21 tp w Cxf).
      unfold ndv. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL tv_fs2 frL bd_s0 (AHead pH true) Es_fs0 rho tp w Cptv Hw).
    - intros tr md HJ HF1. apply Forall_app. split; [|exact HF1]. constructor; [|constructor].
      exact (nnPhi2_holds rho tp tr md HF1 HJ). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ. intros E0'.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [unfold tv_fs2; apply in_or_app; left; exact lines_in_kept_fs2|].
    unfold tnz. cbn [fst]. intros H. exact (H E0'). }
  intros Hnull.
  unfold ndv, tv_fs2.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX FSP.P0_fs PTrue (fun _ H => H) (fun _ _ _ H => H)
           FS.Pre_fs FS.nd0 PDk_fs2 FS.NP eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHF eq_refl
           E_fs2 s_fs2 R_fs2 Xk_fs2 rho tp kept_fs2 passed_fs2 frL bd_s0 brest_fs2 (AHead pH true) (FAM (efmeasA (Es_fs0, nd_s0, 0%nat, (398, z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. unfold payA. exact (pay_okF_split _ _ _ _ bd_s0 (hand_fs2 ++ brest_fs2) bdrest_fs2 payX_fs2 payY_fs2 PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_fs2 rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : ldefR rho') by exact (ldefR_call CST FB FF rho0 E_fs2 kept_fs2 rho rho' HF CLF C500 Hag HK lines_in_kept_fs2 Hnull HPHI).
    pose proof epiS1_checks_nd as (Cndn & Cndo & Cndz & CTn & CTo & CTf & CTz & Bn & Bo & Bz & Tin & Tio & Tiz & _ & _ & _ & CABS).
    cbn [PDk_fs2 liftPD FSP.PD_fs map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[Hd|[]]]]]; injection Hd as <- <- <-; cbn [fst snd].
    + rewrite CTn, Cndn.
      apply (TR_pre (SPA segs (JAv nd_nop2) T_nop2 rho' tp')).
      { intros w Hw. rewrite <- Tin. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_nop2) (xfb_fs2 T_nop20) rho' T_nop20 B_nop2 tp' w Bn Hw). }
      apply (CUTS1 T_nop2 nd_nop2 0%nat (397, z0) rho' tp'); [right; left; reflexivity | exact HPHI' | meas].
    + rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_ok2) T_ok2 rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_ok2) (xfb_fs2 T_ok20) rho' T_ok20 B_ok2 tp' w Bo Hw). }
      apply (CUTS1 T_ok2 nd_ok2 0%nat (397, z0) rho' tp'); [right; right; left; reflexivity | exact HPHI' | meas].
    + rewrite CTf. apply TR_facts. intros HFf. exfalso.
      pose proof (holds_mem _ _ _ HFf CABS) as FA. cbn [holds f_absurd] in FA. apply FA. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + rewrite CTz, Cndz.
      apply (TR_pre (SPA segs (JAv nd_fz2) T_fz2 rho' tp')).
      { intros w Hw. rewrite <- Tiz. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fz2) (xfb_fs2 T_fz20) rho' T_fz20 B_fz2 tp' w Bz Hw). }
      apply (CUTS1 T_fz2 nd_fz2 0%nat (397, z0) rho' tp'); [right; right; right; left; reflexivity | exact HPHI' | meas].
Qed.

Lemma X_L_sn : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S68A2S64R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S64S68A4G1A4S0S21S24Z18cS97A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS1_checks_succ as (_ & _ & _ & _ & Cen & Cidn & _ & _ & Cpn & _ & _ & Ctvn & Cbn & _ & _ & Camn).
  pose proof epiS_chk_succ as (Cnpn & Cnbn & Cfrn & Cphin & _).
  pose proof (phi_sub V_ldR ldefR ldefR_reads s_nn rho Cphin HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv nd_succ) K_succ (rho_sub rho s_nn) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_sn K_succ s_nn (NDA tvL frL bd_nop2 (AHead qHn2 true)) nd_succ rho tp w
             Cen Cidn Cnpn Cnbn Ctvn Cfrn Cbn Camn).
    unfold nd_nop2 in Hw. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_nop2 tvL frL bd_nop2 (AHead qHn2 true) L_sn rho tp w Cpn Hw). }
  apply (CUTS2a K_succ nd_succ 0%nat (395, z0) (rho_sub rho s_nn) tp); [left; reflexivity | exact HPHI' | meas].
Qed.
Lemma X_L_sk : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S69A2S63R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S63S69A4G1A4S0S21S24Z18cS97A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS1_checks_succ as (_ & _ & _ & _ & _ & _ & Cek & Cidk & _ & Cpk & Ctvk & _ & _ & Cbk & Camk & _).
  pose proof epiS_chk_succ as (_ & _ & _ & _ & Cnpk & Cnbk & Cfrk & Cphik & _).
  pose proof (phi_sub V_ldR ldefR ldefR_reads s_kn rho Cphik HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv nd_succ) K_succ (rho_sub rho s_kn) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_sk K_succ s_kn (NDA tvL_k frL bd_ok2 (AHead qHk2 true)) nd_succ rho tp w
             Cek Cidk Cnpk Cnbk Ctvk Cfrk Cbk Camk).
    unfold nd_ok2 in Hw. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_ok2 tvL_k frL bd_ok2 (AHead qHk2 true) L_sk rho tp w Cpk Hw). }
  apply (CUTS2a K_succ nd_succ 0%nat (395, z0) (rho_sub rho s_kn) tp); [left; reflexivity | exact HPHI' | meas].
Qed.
Lemma X_L_dz : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S67A2S62R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S62S67A4G1A4S0S21S24Z18cS97A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & _ & _ & _ & _ & _ & CL). pose proof epiS_chk_landphi as (_ & _ & _ & _ & _ & _ & CP & _). pose proof epiS_chk_succ as (_ & _ & _ & _ & _ & _ & _ & _ & Cpz).
  apply (TR_pre (SPA segs (JAv (NDA tvL frL bd_fz2 (AHead qHz2 false))) L_dz rho tp)).
  { intros w Hw. unfold nd_fz2 in Hw. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fz2 tvL frL bd_fz2 (AHead qHz2 false) L_dz rho tp w Cpz Hw). }
  apply (X_LANDf L_dz bd_fz2 qHz2 _ rho tp tp0 CL CP); [rewrite DP.efmeas_z0; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HPHI].
Qed.

Lemma bnds_hold : ltac2:(tb__ "0|0|
S23S3S25A1S38R2A1S96S25S29R3A1R2A3S33S5S45S25S28Sc3A1R3A3S4A3S33S5S45S25S28Sc2A1R4A3S4A3S33S5S46S25S25S45S25S28R1A1R6A3Lf;Sc1A3S4A3S96S25S29R7A1S76A3F_;F_;F_;F_;F_;FF;Frho;").
Proof using .
  intros rho F HP HF C1 C2 C3.
  destruct (rate2_bounds rho (ldefR_rate rho HP) (holds_mem _ _ _ HF C1) (holds_mem _ _ _ HF C2)) as [B1 B3].
  cbn [cc_facts forallb] in C3. apply andb_prop in C3 as [D1 C3]. apply andb_prop in C3 as [D2 C3]. apply andb_prop in C3 as [D3 C3]. apply andb_prop in C3 as [D4 _].
  pose proof (holds_mem _ _ _ HF D1) as G1. pose proof (holds_mem _ _ _ HF D2) as G2. pose proof (holds_mem _ _ _ HF D3) as G3. pose proof (holds_mem _ _ _ HF D4) as G4.
  rewrite h_ule in G1, G2, G3, G4. rewrite uval_lit in G2, G4 by lia.
  unfold bnds, B32m. cbn [map].
  constructor; [exact B1|]. constructor; [rewrite h_ule, uval_lit by lia; lia|]. constructor; [exact B3|]. constructor; [rewrite h_ule, uval_lit by lia; lia|]. constructor.
Qed.
Lemma X_L_v0 : ltac2:(tb__ "0|1|
SdSdS23S3S2eQ40A1A1M0S21G0S33S5S46S25S2aS86R6A1A1S6S25S76S85R6A1A3A3S4A3S33SdSdeR7S6S25S76S85R7A1A3A2R6A3S33S5S45S25S28Sc3A1S85R8A1A3S4A3S33S5S45S25S28Sc2A1S85R9A1A3S4A3S33S5S46S25S25S45S25S28R1A1S85RbA1A3Lf;Sc1A3S4A3S33S5SdfS66S80A2S4A3S33S5S81RbS79S82S72U1A1A4S4A3S33S5S3dS39SaaS52SeRcA1SeS79A1A3A2S4A3S58S5bS59S47S5aZ2Z40A2A2Z37aA2RaA2VTR;S2fS12VJAFv;S3aS37U0A2S5dA2RfRdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FLb;FL;").
Proof.
  intros L Lb rho tp b tp0 Cfb Cwf Cnx Clen Ccc Cperm HE Cphi Hb. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  destruct (ent_chk2_unf Lb B_1 nd_succP (ndAt 1) HE) as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof (phi_sub V_ldR ldefR ldefR_reads _ rho Cphi HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv (ndAt 1)) B_1 (rho_sub rho (infer_sub NP (ax_S Lb) (ax_S B_1))) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lb B_1 _ nd_succP (ndAt 1) rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    unfold nd_succP. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL bd_succ bd_succP (AHead pH true) Lb rho tp w Cperm).
    rewrite <- Cwf. apply (SPA_refacts_JA segs); [exact Hw | exact Cfb |].
    intros tr md _ HF. apply Forall_app. split; [|exact HF]. exact (bnds_hold rho _ HPHI HF Cnx Clen Ccc). }
  apply (CUTS2b B_1 (ndAt 1) 0%nat (RB, zl 890) _ tp); [left; reflexivity | exact HPHI' |].
  rewrite efmeas_lit by (vm_compute; split; [discriminate | reflexivity]). split; [vm_compute; discriminate | exact Hb].
Qed.

Lemma X_L_rp0g : ltac2:(tb__ "0|1|
SdSdS23S3S2eQ40A1A1M0S21G0S33S5S46S25S2aS86R6A1A1S6S25S76S85R6A1A3A3S4A3S33SdSdeR7S6S25S76S85R7A1A3A2R6A3S33S5S45S25S28Sc3A1S85R8A1A3S4A3S33S5S45S25S28Sc2A1S85R9A1A3S4A3S33S5S46S25S25S45S25S28R1A1S85RbA1A3Lf;Sc1A3S4A3S33S5SdfS66S80A2S4A3S33S5S81RbS73S82S74A4S4A3S33S5S3dS39SaaS52SeRcA1SeS73A1A3A2S4A3S57S5bS59S47S5aZ2Z40A2A2Z37fA2RaA2VTR;S2fS12VJAFv;S3aS37U0A2S5dA2RfRdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FLb;FL;").
Proof.
  intros L Lb rho tp b tp0 Cfb Cwf Cnx Clen Ccc Cperm HE Cphi Hb. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  destruct (ent_chk2_unf Lb K_rp nd_succP nd_rp HE) as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof (phi_sub V_ldR ldefR ldefR_reads _ rho Cphi HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv nd_rp) K_rp (rho_sub rho (infer_sub NP (ax_S Lb) (ax_S K_rp))) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lb K_rp _ nd_succP nd_rp rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    unfold nd_succP. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL bd_succ bd_succP (AHead pH true) Lb rho tp w Cperm).
    rewrite <- Cwf. apply (SPA_refacts_JA segs); [exact Hw | exact Cfb |].
    intros tr md _ HF. apply Forall_app. split; [|exact HF]. exact (bnds_hold rho _ HPHI HF Cnx Clen Ccc). }
  exact (RP _ tp b tp0 HPHI' Hb).
Qed.

Lemma X_L_w : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S5dA2S77R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S77S5dA4G1A4S0S21S24Z18aS48Z1eA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS_chk_w as (Cbase & Chf & Cswf & Ceq & CR & _).
  apply (TR_pre (SPA segs (JAv nd_succ) T_wr rho tp)).
  { intros w Hw. rewrite <- Ceq. unfold nd_succ.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             tvL frL bd_succ (AHead pH true) 0%nat 110%positive 5 120%positive g5 wK1 wK2 L_w (ax_X L_w) rho tp w eq_refl c5_ok Cbase kw1 kw12 Chf (fun r H => H) Cswf); [|exact Hw].
    intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    - exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
    - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tvL (ax_X L_w) rho3 tp3 md3 wK1 wK2 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_w). }
  apply (CUTS2a T_wr nd_succ 0%nat (394, zl 20) rho tp); [right; left; reflexivity | exact HPHI | meas].
Qed.

Lemma X_E_wm0 : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S5dA2S7eR3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S7eS5dA4G1A4S0S21S24Z18aS48Z13A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS_chk_wm as (Cbase & Cobjs & Chf & Cloc & Cnb0 & CR0 & CLF0 & Ceqr & Cxf & Cent & Cchk & Cta & Cnp & Cnb & Cbb & Cwp & Cpp & CR & CX & CLF & C500 & CT0 & CxB & Ctidy & _).
  apply TR_facts. intros HF0.
  apply (TR_pre (fun w => exists rho1, ldefR rho1 /\ SPA segs (JAv nd_succ) E_wm rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 wK1 wK2 wcells DUnknown] (vms md tp ms)). split.
    - destruct Hw as [Hsm (Ai & kc & HJ)].
      pose proof (has_facts_sound rho _ _ HF0 Chf) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
      exact (ldefR_absorb_sh AInv CST XGL ALA HCST Kc FB FF BX rho0 nd_succ Ai kc rho tp tr md 0%nat 110%positive 5 120%positive g5 wK1 wK2 wcells DUnknown (vms md tp ms)
               HJ eq_refl c5_ok kw1 kw12 HG1 HG2 lines_in_tvL (ldef_facts_k64 rho _ HF0 CLF0) HPHI).
    - apply (SPA_axforms segs (JAv nd_succ) (xf_w E_wmr) _ E_wmr E_wm tp _ Cxf). rewrite <- Ceqr. unfold nd_succ.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL bd_succ (AHead pH true) 0%nat 110%positive 5 120%positive g5 wK1 wK2 wcells DUnknown E_wm0 (objs_butlast E_wm0) [(wOff, wLen)] rho tp tr ms md
               eq_refl c5_ok Cbase Cobjs kw1 kw12 eq_refl Chf Cloc Cnb0); [|exact Hw].
      intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
      exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR0). }
  apply TR_exw. intros rho1.
  apply (TR_pureP _ (ldefR rho1)); [intros w [H _]; exact H|]. intros HPHI1.
  apply (TR_pre (SPA segs (JAv nd_succ) E_wm rho1 tp)); [intros w [_ Hw]; exact Hw|].
  apply TR_facts. intros HF1.
  apply (TR_pureP _ (uval rho1 xLD = 0 -> uval rho1 szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv nd_succ] in HZ. intros E0'.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL) lines_in_tvL). unfold tnz. cbn [fst]. intros H. exact (H E0'). }
  intros Hnull.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_build_line_index_rom_call.purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           (fun _ _ => True) PreR [LR] E_wm (s_w E_wm) (R_w E_wm) rho1 tp nd_succ bd_succ (FAM (efmeasA (E_wm0, nd_succ, 0%nat, (394, zl 19)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. exact (CMEMCPYR Ai rho2 tp2).
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - cbn [nd_bd nd_succ]. apply payA_same. exact Cwp.
  - exact Cpp.
  - exact (DP.site_rt_lo0 AInv CST XGL ALA HCST HXlits FB FF rho0 E_wm (s_w E_wm) (R_w E_wm) rho1 tvL bd_succ (AHead pH true) CR CX).
  - intros Ai tr ms md _ _ _. exact I.
  - intros L' rho2 tp2 HL Hag HKR. destruct HL as [<-|[]]. cbn [nd_tv nd_fr nd_am nd_succ].
    change (T_afterA PreR E_wm (s_w E_wm) (R_w E_wm) LR) with (T_wc E_wm). rewrite CT0.
    pose proof (ldefR_keptR E_wm tvL rho1 rho2 HF1 CLF C500 Hag HKR lines_in_tvL Hnull HPHI1) as HPHI2.
    apply (TR_pre (SPA segs (JAv nd_succ) T_wm rho2 tp2)).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_succ) (xfb_w T_wm0) rho2 T_wm0 T_wmb tp2 w CxB Hw). }
    apply (CUTS2a T_wm nd_succ 0%nat (394, zl 10) rho2 tp2); [right; right; left; reflexivity | exact HPHI2 | meas].
Qed.

Lemma X_L_rpx : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S74A2S7fR3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S7fS74A4G1A4S0S21S24S47S48Z37dA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS_chk_rpx as (Cbase & Cobjs & Chf & Cnb0 & CR0 & CLF0 & Ceqr & HE & Cphi & _).
  apply TR_facts. intros HF0.
  apply (TR_pre (fun w => exists rho1, ldefR rho1 /\ SPA segs (JAv nd_rp) L_rpc rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 wK1 wK2 pcells DUnknown] (vms md tp ms)). split.
    - destruct Hw as [Hsm (Ai & kc & HJ)].
      pose proof (has_facts_sound rho _ _ HF0 Chf) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
      exact (ldefR_absorb_sh AInv CST XGL ALA HCST Kc FB FF BX rho0 nd_rp Ai kc rho tp tr md 0%nat 110%positive 5 120%positive g5 wK1 wK2 pcells DUnknown (vms md tp ms)
               HJ eq_refl c5_ok kw1 kw12 HG1 HG2 lines_in_tvL (ldef_facts_k64 rho _ HF0 CLF0) HPHI).
    - rewrite <- Ceqr. unfold nd_rp, ndAt.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL (bdAt 1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 wK1 wK2 pcells DUnknown L_rpx (objs_butlast L_rpx) [] rho tp tr ms md
               eq_refl c5_ok Cbase Cobjs kw1 kw12 eq_refl Chf eq_refl Cnb0); [|exact Hw].
      intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
      exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR0). }
  apply TR_exw. intros rho1.
  apply (TR_pureP _ (ldefR rho1)); [intros w [H _]; exact H|]. intros HPHI1.
  apply (TR_pre (SPA segs (JAv nd_rp) L_rpc rho1 tp)); [intros w [_ Hw]; exact Hw|].
  destruct (ent_chk2_unf L_rpc B_1 nd_rp (ndAt 1) HE) as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof (phi_sub V_ldR ldefR ldefR_reads _ rho1 Cphi HPHI1) as HPHI1'.
  apply (TR_pre (SPA segs (JAv (ndAt 1)) B_1 (rho_sub rho1 (infer_sub NP (ax_S L_rpc) (ax_S B_1))) tp)).
  { intros w Hw. exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_rpc B_1 _ nd_rp (ndAt 1) rho1 tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUTS2b B_1 (ndAt 1) 0%nat (RB, zl 890) _ tp); [left; reflexivity | exact HPHI1' | meas].
Qed.

Lemma fail_potin : ltac2:(tb__ "0|2|
SdS3S9eA1M0G0S53S23S3S2eQ40A1A1S33S5S40S27SeR6A1A1S6S9eR5S83A3R4A3S4A3VTR;S2fS12VJAv;S17S93S92R6S16Sc7S4A2A4A1R7R3R2A5R4A2VTR;S2fS12VJAv;S17S6S1S24S24A2M1S84S8G1Se6S9G1A1A3A3S92R6S16Sc7SbA2A4A1R8R4R3A5R5A2F_;F_;Ftp;Frho;FQ;Fbrest;Fbdn;FTf;").
Proof.
  intros Tf bdn brest Q rho tp Hle H. apply (TR_pre (SPA segs (JAv (NDA tvL frL bdn (AHead pH true))) Tf rho tp)); [|exact H]. intros w Hw.
  apply (SPA_JA_pot_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL bdn pH Tf rho tp w (BXok_d_nn 7 BX HBX)).
  exact (SPA_JA_le2 segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL brest (bdn ++ ENDOWs) (AHead pH false) Tf rho tp w Hle Hw).
Qed.
Ltac xblk CHK E0 E Tz0 TzB Tz Tf0 TfB Tf Tk0 TkB Tk Ty0 TyB Ty R d e k o bcom dupj dupn qHk rho tp HPHI :=
  pose proof CHK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26
                     & C27 & C28 & C29 & C30 & C31 & C32 & C33 & C34 & C35 & C36 & C37 & C38 & C39 & C40 & C41 & C42 & C43 & C44 & C45 & C46 & C47 & C48 & C49 & C50 & C51 & C52);
  apply (X_BLK AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 TR TR_facts TR_ex TR_pre TR_pureP TR_callP CVF
           E0 E Tz0 TzB Tz Tf0 TfB Tf Tk0 TkB Tk Ty0 TyB Ty R d e k o bcom dupj dupn qHk _ rho tp
           ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(lia) ltac:(lia)
           C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36
           C37 C38 C39 C40 C41 C42 C43 C44 C45 C46); [ | | | | exact HPHI].
Lemma X_E0_1 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U1A1M2A2Sd4R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sd4G2A4G1A4S0S21S24S47S48Z379A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 1) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 1) (kAt 1) ++ dupAt 1) (AHead pH true)).
  xblk st_chk_1 E0_1 E_1 Tz0_1 TzB_1 Tz_1 Tf0_1 TfB_1 Tf_1 Tk0_1 TkB_1 Tk_1 Ty0_1 TyB_1 Ty_1 R_1 (SVar 400) 4 (SVar 402) 568 (bd_com (cAt 1) (kAt 1)) (dupAt 1) (dupAt 2) qHk_1 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tz_1 (ndZ 1) 0%nat (RB, zl 888) rho' tp'); [do 2 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_1 (bdAt 2) (bd_com (cAt 1) (kAt 1) ++ dupAt 2) _ rho' tp' C52).
    apply (CUTS2b Tf_1 (ndAt 2) 0%nat (RB, zl 888) rho' tp'); [do 3 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Tk_1 (ndK 1 qHk_1) 0%nat (RB, zl 888) rho' tp'); [do 4 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Ty_1 (ndZ 1) 0%nat (RB, zl 888) rho' tp'); [do 5 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_2 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U2A1M2A2Sd5R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sd5G2A4G1A4S0S21S24S47S48Z36fA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 2) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 2) (kAt 2) ++ dupAt 2) (AHead pH true)).
  xblk st_chk_2 E0_2 E_2 Tz0_2 TzB_2 Tz_2 Tf0_2 TfB_2 Tf_2 Tk0_2 TkB_2 Tk_2 Ty0_2 TyB_2 Ty_2 R_2 (SVar 403) 4 (SVar 405) 600 (bd_com (cAt 2) (kAt 2)) (dupAt 2) (dupAt 3) qHk_2 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tz_2 (ndZ 2) 0%nat (RB, zl 878) rho' tp'); [do 7 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_2 (bdAt 3) (bd_com (cAt 2) (kAt 2) ++ dupAt 3) _ rho' tp' C52).
    apply (CUTS2b Tf_2 (ndAt 3) 0%nat (RB, zl 878) rho' tp'); [do 8 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Tk_2 (ndK 2 qHk_2) 0%nat (RB, zl 878) rho' tp'); [do 9 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Ty_2 (ndZ 2) 0%nat (RB, zl 878) rho' tp'); [do 10 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_3 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U3A1M2A2Sd6R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sd6G2A4G1A4S0S21S24S47S48Z365A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 3) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 3) (kAt 3) ++ dupAt 3) (AHead pH true)).
  xblk st_chk_3 E0_3 E_3 Tz0_3 TzB_3 Tz_3 Tf0_3 TfB_3 Tf_3 Tk0_3 TkB_3 Tk_3 Ty0_3 TyB_3 Ty_3 R_3 (SVar 406) 4 (SVar 408) 632 (bd_com (cAt 3) (kAt 3)) (dupAt 3) (dupAt 4) qHk_3 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tz_3 (ndZ 3) 0%nat (RB, zl 868) rho' tp'); [do 12 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_3 (bdAt 4) (bd_com (cAt 3) (kAt 3) ++ dupAt 4) _ rho' tp' C52).
    apply (CUTS2b Tf_3 (ndAt 4) 0%nat (RB, zl 868) rho' tp'); [do 13 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Tk_3 (ndK 3 qHk_3) 0%nat (RB, zl 868) rho' tp'); [do 14 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Ty_3 (ndZ 3) 0%nat (RB, zl 868) rho' tp'); [do 15 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_4 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U4A1M2A2Sd7R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sd7G2A4G1A4S0S21S24S47S48Z35bA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 4) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 4) (kAt 4) ++ dupAt 4) (AHead pH true)).
  xblk st_chk_4 E0_4 E_4 Tz0_4 TzB_4 Tz_4 Tf0_4 TfB_4 Tf_4 Tk0_4 TkB_4 Tk_4 Ty0_4 TyB_4 Ty_4 R_4 (SVar 409) 4 (SVar 411) 664 (bd_com (cAt 4) (kAt 4)) (dupAt 4) (dupAt 5) qHk_4 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tz_4 (ndZ 4) 0%nat (RB, zl 858) rho' tp'); [do 17 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_4 (bdAt 5) (bd_com (cAt 4) (kAt 4) ++ dupAt 5) _ rho' tp' C52).
    apply (CUTS2b Tf_4 (ndAt 5) 0%nat (RB, zl 858) rho' tp'); [do 18 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Tk_4 (ndK 4 qHk_4) 0%nat (RB, zl 858) rho' tp'); [do 19 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Ty_4 (ndZ 4) 0%nat (RB, zl 858) rho' tp'); [do 20 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_5 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U5A1M2A2Sd8R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sd8G2A4G1A4S0S21S24S47S48Z351A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 5) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 5) (kAt 5) ++ dupAt 5) (AHead pH true)).
  xblk st_chk_5 E0_5 E_5 Tz0_5 TzB_5 Tz_5 Tf0_5 TfB_5 Tf_5 Tk0_5 TkB_5 Tk_5 Ty0_5 TyB_5 Ty_5 R_5 (SVar 412) 4 (SVar 414) 696 (bd_com (cAt 5) (kAt 5)) (dupAt 5) (dupAt 6) qHk_5 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tz_5 (ndZ 5) 0%nat (RB, zl 848) rho' tp'); [do 22 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_5 (bdAt 6) (bd_com (cAt 5) (kAt 5) ++ dupAt 6) _ rho' tp' C52).
    apply (CUTS2b Tf_5 (ndAt 6) 0%nat (RB, zl 848) rho' tp'); [do 23 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Tk_5 (ndK 5 qHk_5) 0%nat (RB, zl 848) rho' tp'); [do 24 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Ty_5 (ndZ 5) 0%nat (RB, zl 848) rho' tp'); [do 25 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_6 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U6A1M2A2Sd9R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sd9G2A4G1A4S0S21S24S47S48Z347A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 6) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 6) (kAt 6) ++ dupAt 6) (AHead pH true)).
  xblk st_chk_6 E0_6 E_6 Tz0_6 TzB_6 Tz_6 Tf0_6 TfB_6 Tf_6 Tk0_6 TkB_6 Tk_6 Ty0_6 TyB_6 Ty_6 R_6 (SVar 415) 4 (SVar 417) 728 (bd_com (cAt 6) (kAt 6)) (dupAt 6) (dupAt 7) qHk_6 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tz_6 (ndZ 6) 0%nat (RB, zl 838) rho' tp'); [do 27 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_6 (bdAt 7) (bd_com (cAt 6) (kAt 6) ++ dupAt 7) _ rho' tp' C52).
    apply (CUTS2b Tf_6 (ndAt 7) 0%nat (RB, zl 838) rho' tp'); [do 28 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Tk_6 (ndK 6 qHk_6) 0%nat (RB, zl 838) rho' tp'); [do 29 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Ty_6 (ndZ 6) 0%nat (RB, zl 838) rho' tp'); [do 30 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_8 : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2SbfA2Sb7R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13Sb7SbfA4G1A4S0S21S24S47S48Z333A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (nd8) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 7) (kAt 7) ++ dupAt 7) (AHead pH true)).
  xblk st_chk_8 E0_8 E_8 Tz0_8 TzB_8 Tz_8 Tf0_8 TfB_8 Tf_8 Tk0_8 TkB_8 Tk_8 Ty0_8 TyB_8 Ty_8 R_8 (SVar 418) 128 (SVar 420) 896 (bd_com (cAt 7) (kAt 7)) (dupAt 7) (dup8) qHk_8 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS4 Tz_8 (ndZ8) 0%nat (RB, zl 818) rho' tp'); [do 2 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_8 (bd9) (bd_com (cAt 7) (kAt 7) ++ dup8) _ rho' tp' C52).
    apply (CUTS4 Tf_8 (nd9) 0%nat (RB, zl 818) rho' tp'); [do 3 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS4 Tk_8 (ndK8) 0%nat (RB, zl 818) rho' tp'); [do 4 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS4 Ty_8 (ndZ8) 0%nat (RB, zl 818) rho' tp'); [do 5 right; left; reflexivity | exact HP' | meas].
Qed.

Ltac above390 := rewrite ?DP.efmeas_z0, ?efmeas_lit by (vm_compute; split; [discriminate | reflexivity]); vm_compute; reflexivity.
Lemma X_L_land : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2Sc0A2SbdR3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13SbdSc0A4G1A4S0S21S24S47S48Z325A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (CL & _ & _ & _ & _ & _ & _). pose proof epiS_chk_landphi as (CP & _ & _ & _ & _ & _ & _ & _).
  apply (X_LANDt L_land (bd9) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_L_d7 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U7A1M2A2SbcR3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13SbcG2A4G1A4S0S21S24S47S48Z33dA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & CL & _ & _ & _ & _ & _). pose proof epiS_chk_landphi as (_ & CP & _ & _ & _ & _ & _ & _).
  apply (X_LANDt L_d7 (bdAt 7) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_L_d1 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U1A1M2A2SdaR3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13SdaG2A4G1A4S0S21S24S47S48Z379A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & _ & CL & _ & _ & _ & _). pose proof epiS_chk_landphi as (_ & _ & CP & _ & _ & _ & _ & _).
  apply (X_LANDt L_d1 (bdAt 1) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_L_d6z : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S4dU6A1M2A2SbbR3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13SbbG2A4G1A4S0S21S24S47S48Z345A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & _ & _ & CL & _ & _ & _). pose proof epiS_chk_landphi as (_ & _ & _ & CP & _ & _ & _ & _).
  apply (X_LANDt L_d6z (brestAt 6) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_L_d6y : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S4dU6A1M2A2SbaR3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13SbaG2A4G1A4S0S21S24S47S48Z345A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & _ & _ & _ & CL & _ & _). pose proof epiS_chk_landphi as (_ & _ & _ & _ & CP & _ & _ & _).
  apply (X_LANDt L_d6y (brestAt 6) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_L_d6f : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U7A1M2A2Sb9R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sb9G2A4G1A4S0S21S24S47S48Z345A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & _ & _ & _ & _ & CL & _). pose proof epiS_chk_landphi as (_ & _ & _ & _ & _ & CP & _ & _).
  apply (X_LANDt L_d6f (bdAt 7) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_E_fu0 : ltac2:(tb__ "0|4|
S23S3S2eQ40A1A1M0G0VTR;S2fS12VJAFv;S3aS37U0M1A2S72U7A1M2A2Sb8R3R2A5VFAM;S3bS0S1S1SdS13A2M3S2A2S1S21S24A2S0G3S2S0SdS13Sb8G2A4G1A4S0S21S24S47S48Z33dA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_fu as (_ & Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CT0 & CxB & Ctidy & _).
  pose proof epiS_chk_fu as (C500 & _).
  apply (TR_pre (SPA segs (JAv (ndAt 7)) E_fu rho tp)).
  { intros w Hw. exact (SPA_axforms segs (JAv (ndAt 7)) (xf_fu E_fu0) rho E_fu0 E_fu tp w Cxf Hw). }
  apply (PURE_fu E_fu s_fu R_fu rho tp (ndAt 7) _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In FU.Posts_fu] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite CT0.
  pose proof (ldefR_pure E_fu rho rho' C500 Hag HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv (ndAt 7)) T_fu rho' tp)).
  { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs (JAv (ndAt 7)) (xfb_fu T_fu0) rho' T_fu0 B_fu tp w CxB Hw). }
  apply (CUTS4 T_fu (ndAt 7) 0%nat (RB, zl 828) rho' tp); [left; reflexivity | exact HPHI' | meas].
Qed.

Lemma exitsS1_ok : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4eA3VTR;S2fS12VJAFv;S3aS37R6A2R7A2R8R4R3A5VFAM;S3bS0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS1 In] in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-.
  - apply X_Es_fs0.
  - apply X_L_sn.
  - apply X_L_sk.
  - apply X_L_dz.
Qed.
Lemma exitsS2a_ok : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4fA3VTR;S2fS12VJAFv;S3aS37R6A2R7A2R8R4R3A5VFAM;S3bS0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS2a In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <- <- <-.
  - pose proof epiS_chk_v0 as (Cfb & Cwf & Cnx & Clen & Ccc & Cperm & HE & Cphi & _).
    apply (X_L_v0 L_v0a Lb_v0a rho tp _ tp0 Cfb Cwf Cnx Clen Ccc Cperm HE Cphi). rewrite DP.efmeas_z0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply X_L_w.
  - apply X_E_wm0.
  - apply CONT_cf.
  - pose proof epiS_chk_v0 as (_ & _ & _ & _ & _ & Cperm & _ & _ & Cfb & Cwf & Cnx & Clen & Ccc & HE & Cphi).
    apply (X_L_rp0g L_rp0 Lb_rp0 rho tp _ tp0 Cfb Cwf Cnx Clen Ccc Cperm HE Cphi). rewrite DP.efmeas_z0. unfold RB. vm_compute. discriminate.
Qed.
Lemma exitsS2b_ok : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S50A3VTR;S2fS12VJAFv;S3aS37R6A2R7A2R8R4R3A5VFAM;S3bS0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS2b In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <- <- <-.
  - apply X_L_rpx.
  - apply X_E0_1.
  - apply X_E0_2.
  - apply X_E0_3.
  - apply X_E0_4.
  - apply X_E0_5.
  - apply X_E0_6.
  - apply X_L_d6f.
  - apply X_L_d6z.
  - apply X_L_d6y.
  - apply X_L_d7.
  - apply X_E_fu0.
  - apply X_L_d1.
Qed.
Lemma exitsS4_ok : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S51A3VTR;S2fS12VJAFv;S3aS37R6A2R7A2R8R4R3A5VFAM;S3bS0G3G0S0G2S2S0SdS13R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS4 In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply X_E0_8.
  - apply X_L_land.
Qed.
End X.

Let frozen_stable : ltac2:(tb__ "0|0|
S22S22S13S23ScfS52R3A2S33S5S18R4R3A2S4A3S32S12R6S1eVAInv;VCST;VXGL;S52VKc;Vrho0;VP0;VFB;VFF;VBX;S14R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
Se3VAInv;VCST;VXGL;VALA;S52VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S1fS12VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SaeS12SabVAInv;VCST;VXGL;A5").
Hypothesis MCROML : ltac2:(tb__ "0|0|
Sd1S12SabVAInv;VCST;VXGL;Sd0ZcA7").
Variable FAMQ : list word -> assn.
Hypothesis KDISP_T : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0G0S94R3A1S55S12Vok;S2fS12VJAv;Sb6A1Sa1R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").

Lemma CHF_T : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S9dS23S3S2eQ40A1A1S9cZ5R3A2S55S12Vok;S2fS12S15VAInv;VCST;VXGL;VKc;S98R6R5A2R6R5R4S14Sb5AaSb4R3R2A5S87S12Sb3R3R2Sa0VAInv;VCST;VXGL;VKc;S98S14S60R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs2.
  eapply (sum_PostsC_k segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (FSP.finalize_shape_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.
Lemma CVF_T : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S9dS23S3S2eQ40A1A1S9cZ4R3A2S55S12Vok;S2fS12S15VAInv;VCST;VXGL;VKc;S99VCST;R6R5A3R6R5R4S14Sc5AaSc4R3R2A5S87S12S9bR3R2Sa0VAInv;VCST;VXGL;VKc;S99VCST;A1S14S7bR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vf.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (VFP.P0_vf CST) PTrue VF.Pre_vf VF.nd0 VFP.PD_vf NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (VFP.vec_finalize_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.
Lemma PURE_fu_T : ltac2:(tb__ "0|2|
SdSa5S3S2bA1M0S23S3S2eQ40A1A1S13S53S33SaG0A1S89R7S90R6A3S7G0R5A2A3S33S5S8aR8S90R7R6S95SfSdS10S91A4A5S4A3S33S5SceS52S26SeR9A1A1A2S4A3S33S5S18S26SeRaA1A1R5A2S4A3S33S5S46S25S2aS26SeRbA1M1A1A1S27G1A1A3S4A3SfS23S44SfR2S91A3S2cS26SeRfA1A1RcR2A3S55S12Vok;S2fS12VJAv;RbA1ScaS27SeR10A1A1S8bRfS90S10R4A1R10ReA5A2R3RcA5RaA4F_;F_;Frho';FL;S55S12Vok;S2fS12VJAv;R8A1RdRaR9A5R7A4F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl FU.Pre_fu s R FU.Posts_fu rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply FU.finalize_unknowns_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma CMEMCPYR_T : ltac2:(tb__ "0|2|
Sa6S23S3S2eQ40A1A1M0S55S12Vok;S2fS12S23G0S3S8fA1S8eS34SadVAInv;R7VKc;R4R3R2R1A7S35A2Lm;Lt;Lp;Lr;S7cR2R1A5S87S12S9bR2R1S8S1SdS88A2M1S0SdS88S7aSacVAInv;VCST;VXGL;R3VKc;A5A4S9G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof using HKc Hok MCROML.
  intros Ai rho1 tp1. eapply triple_conseq; [| intros w Hw; exact Hw |].
  2: { apply (MCROML ok Ai Kc rho1 tp1 HKc). eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. }
  intros [tr [ms md]] [Hsm [HJ _]]. split; [exact Hsm | exact HJ].
Qed.

Let famS (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S21S3S2eQ40A1A1S56S36SecS12S95S3eSccS43VAInv;VCST;VXGL;S52VKc;Vrho0;VP0;VFB;VFF;VBX;S14S37AcS95S3cS3eS41Vcuts;A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|6|
S3S1S1S1SdS13A2M0S2A2M1S1S21S24A2M2A2M3A1S3S2eQ40A1A1M4SdS13S2G2S23G4S21G4S44G3S0G1G2S0G0S2S0SdS13R8R7A4R6A4R5A4RaA3S3aS37R7R5A3S34S57Z0S3bS0G1G2S0G0S2S0SdS13RaR9A4R8A4R7A4R6A2M5A2S58G5R4A2A2S55S12Vok;S2fS12VJAv;RaA1RbR7R6A5VfamS;RdRcR5R4A4A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS ok (map efdrop cuts) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S3S3cA1S3S2eQ40A1A1M0S53S21G0S55S12Vok;R3VFAMQ;R4A1A4S55S12Vok;R4VfamS;R6R5R3R2A4A4F_;Ftp0';Fb;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma S4_T : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4cA3S3aS37R6R4A3S55S12Vok;S2fS12VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS4_ok 300%nat cps_c NP cutsS4 exitsS4 ok (FAMQ tp0) Hok
           ecertS4_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS4_ok (triple segs ok) (famS cutsS4 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CVF_T (reenterS cutsS4 tp0)
           (fun rho tp b tp0' HL _ => rightS cutsS4 tp0 _ b tp0' (KDISP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma S2b_T : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4bA3S3aS37R6R4A3S55S12Vok;S2fS12VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2b_ok 300%nat cps_b NP cutsS2b exitsS2b ok (FAMQ tp0) Hok
           ecertS2b_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS2b_ok (triple segs ok) (famS cutsS2b tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CVF_T (fun Cl s R rho tp nd Q => PURE_fu_T Cl s R rho tp nd Q) (reenterS cutsS2b tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsS2b tp0 _ b tp0' (S4_T T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL _ => rightS cutsS2b tp0 _ b tp0' (KDISP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiS_RP_T : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0G0S38R3A1S55S12Vok;S2fS12VJAv;S74A1S73R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  pose proof epiS_chk_rp as (Cbase & Chf & Cincl & Cswf & Ceq & CR & _).
  eapply triple_conseq; [| intros w Hw; exact Hw | exact (S2b_T T_rp nd_rp 0%nat (RB, zl 894) rho tp tp0 ltac:(right; left; reflexivity) HL)].
  intros w Hw. rewrite <- Ceq. unfold nd_rp, ndAt.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
           tvL frL (bdAt 1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 wK1 wK2 K_rp (ax_X B_1) rho tp w eq_refl c5_ok Cbase kw1 kw12 Chf
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xrs_inclb_sound _ _ Cincl) Cswf); [|exact Hw].
  intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
  - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tvL (ax_X B_1) rho3 tp3 md3 wK1 wK2 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_rp).
Qed.
Hypothesis CONT_cf_T : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0G0S55S12Vok;S2fS12VJAFv;S3aS37U0A2S5dA2S75R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Lemma S2a_T : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4aA3S3aS37R6R4A3S55S12Vok;S2fS12VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2a_ok 300%nat cps_b NP cutsS2a exitsS2a ok (FAMQ tp0) Hok
           ecertS2a_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS2a_ok (triple segs ok) (famS cutsS2a tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CMEMCPYR_T (reenterS cutsS2a tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsS2a tp0 _ b tp0' (S2b_T T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp tp0' => rightS cutsS2a tp0 _ _ tp0' (CONT_cf_T rho tp tp0))
           (fun rho tp b tp0' HL _ => rightS cutsS2a tp0 _ b tp0' (epiS_RP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma S1_T : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S49A3S3aS37R6R4A3S55S12Vok;S2fS12VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS1_ok 300%nat cps_s NP cutsS1 exitsS1 ok (FAMQ tp0) Hok
           ecertS1_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS1_ok (triple segs ok) (famS cutsS1 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHF_T (reenterS cutsS1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsS1 tp0 _ b tp0' (S2a_T T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL _ => rightS cutsS1 tp0 _ b tp0' (KDISP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiS_T : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0G0S38R3A1S55S12Vok;S2fS12VJAv;S5fA1Sc6R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (S1_T K_after0 nd_s0 0%nat (399, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SafS12SabVAInv;VCST;VXGL;A5").
Hypothesis MCROMLX : ltac2:(tb__ "0|0|
Sd2S12SabVAInv;VCST;VXGL;Sd0ZcA7").
Variable FAM : ltac2:(tb__ "0|0|
S21S3S2eQ40A1A1S53F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S21S21S3S2eQ40A1A1S56S57R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis KDISP_E : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0G0S94R3A1S54S12S2fS12VJAv;Sb6A1Sa1R4R3A5VFAM;S59Z186S5aZ2Z40A2A2R2A2A3F_;Ftp0;Ftp;Frho;").

Lemma CHF_E : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S9dS23S3S2eQ40A1A1S9cZ5R3A2S54S12S2fS12S15VAInv;VCST;VXGL;VKc;S98R6R5A2R6R5R4S14Sb5AaSb4R3R2A5S87S12Sb3R3R2Sa0VAInv;VCST;VXGL;VKc;S98S14S60R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs2.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (FSP.finalize_shape_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.
Lemma CVF_E : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S9dS23S3S2eQ40A1A1S9cZ4R3A2S54S12S2fS12S15VAInv;VCST;VXGL;VKc;S99VCST;R6R5A3R6R5R4S14Sc5AaSc4R3R2A5S87S12S9bR3R2Sa0VAInv;VCST;VXGL;VKc;S99VCST;A1S14S7bR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vf.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (VFP.P0_vf CST) PTrue VF.Pre_vf VF.nd0 VFP.PD_vf NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (VFP.vec_finalize_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.
Lemma PURE_fu_E : ltac2:(tb__ "0|2|
SdSa5S3S2bA1M0S23S3S2eQ40A1A1S13S53S33SaG0A1S89R7S90R6A3S7G0R5A2A3S33S5S8aR8S90R7R6S95SfSdS10S91A4A5S4A3S33S5SceS52S26SeR9A1A1A2S4A3S33S5S18S26SeRaA1A1R5A2S4A3S33S5S46S25S2aS26SeRbA1M1A1A1S27G1A1A3S4A3SfS23S44SfR2S91A3S2cS26SeRfA1A1RcR2A3S54S12S2fS12VJAv;RbA1ScaS27SeR10A1A1S8bRfS90S10R4A1R10ReA5A2R3RcA5RaA3F_;F_;Frho';FL;S54S12S2fS12VJAv;R8A1RdRaR9A5R7A3F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl FU.Pre_fu s R FU.Posts_fu rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply FU.finalize_unknowns_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma CMEMCPYR_E : ltac2:(tb__ "0|2|
Sa6S23S3S2eQ40A1A1M0S54S12S2fS12S23G0S3S8fA1S8eS34SadVAInv;R7VKc;R4R3R2R1A7S35A2Lm;Lt;Lp;Lr;S7cR2R1A5S87S12S9bR2R1S8S1SdS88A2M1S0SdS88S7aSacVAInv;VCST;VXGL;R3VKc;A5A4S9G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof using HKc MCROMLX.
  intros Ai rho1 tp1. eapply etriple_conseq; [| intros w Hw; exact Hw | apply (MCROMLX Ai Kc rho1 tp1 HKc)].
  intros [tr [ms md]] [Hsm [HJ _]]. split; [exact Hsm | exact HJ].
Qed.

Let famE (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S21S3S2eQ40A1A1S56S36SebS12S95S3cScbS42VAInv;VCST;VXGL;S52VKc;Vrho0;VP0;VFB;VFF;VBX;S14S37AcVcuts;A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|6|
S3S1S1S1SdS13A2M0S2A2M1S1S21S24A2M2A2M3A1S3S2eQ40A1A1M4SdS13S2G2S23G4S21G4S44G3S0G1G2S0G0S2S0SdS13R8R7A4R6A4R5A4RaA3S3aS37R7R5A3S34S57Z0S3bS0G1G2S0G0S2S0SdS13RaR9A4R8A4R7A4R6A2M5A2S58G5R4A2A2S54S12S2fS12VJAv;RaA1RbR7R6A5VfamE;RdRcR5R4A4A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS cuts T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S3S3cA1S3S2eQ40A1A1M0S53S21S21G0S57R3R2A2S54S12R5VFAM;R4R6A2A3S54S12R6VfamE;R8R7R4R3A4A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma S4_E : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4cA3S3aS37R6R4A3S54S12S2fS12VJAv;R8A1R9R5R4A5VFAM;S3bS0G3G0S0G2S2S0SdS13R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS4_ok 300%nat cps_c NP cutsS4 exitsS4 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS4_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS4_ok (etriple segs) (famE cutsS4 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CVF_E (reenterE cutsS4 tp0)
           (fun rho tp b tp0' HL Hb => rightE cutsS4 tp0 _ _ b tp0' (Z.lt_le_incl _ _ Hb) (KDISP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma S2b_E : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4bA3S3aS37R6R4A3S54S12S2fS12VJAv;R8A1R9R5R4A5VFAM;S3bS0G3G0S0G2S2S0SdS13R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2b_ok 300%nat cps_b NP cutsS2b exitsS2b (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS2b_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS2b_ok (etriple segs) (famE cutsS2b tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CVF_E (fun Cl s R rho tp nd Q => PURE_fu_E Cl s R rho tp nd Q) (reenterE cutsS2b tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsS2b tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (S4_E T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL Hb => rightE cutsS2b tp0 _ _ b tp0' (Z.lt_le_incl _ _ Hb) (KDISP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Theorem epiS_RP_E : ltac2:(tb__ "0|1|
S23S3S2eQ40A1A1M0G0S38R3A1S54S12S2fS12VJAv;S74A1S73R4R3A5VFAM;S5bS59S47S5aZ2Z40A2A2Z37fA2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  pose proof epiS_chk_rp as (Cbase & Chf & Cincl & Cswf & Ceq & CR & _).
  pose proof (S2b_E T_rp nd_rp 0%nat (RB, zl 894) rho tp tp0 ltac:(right; left; reflexivity) HL) as HS2b.
  eapply etriple_conseq; [| | exact HS2b].
  2:{ intros w Hw. refine (FAM_mono _ _ tp0 w _ Hw). rewrite efmeas_lit by (vm_compute; split; [discriminate | reflexivity]). unfold RB. vm_compute. discriminate. }
  intros w Hw. rewrite <- Ceq. unfold nd_rp, ndAt.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
           tvL frL (bdAt 1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 wK1 wK2 K_rp (ax_X B_1) rho tp w eq_refl c5_ok Cbase kw1 kw12 Chf
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xrs_inclb_sound _ _ Cincl) Cswf); [|exact Hw].
  intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
  - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tvL (ax_X B_1) rho3 tp3 md3 wK1 wK2 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_rp).
Qed.
Hypothesis CONT_cf_E : ltac2:(tb__ "0|3|
S23S3S2eQ40A1A1M0G0S54S12S2fS12VJAFv;S3aS37U0M1A2S5dA2S75R3R2A5VFAM;S3bS0S1S1SdS13A2M2S2A2S1S21S24A2S0G2S2S0SdS13S75S5dA4G1A4S0S21S24Z18aS97A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Lemma S2a_E : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S4aA3S3aS37R6R4A3S54S12S2fS12VJAv;R8A1R9R5R4A5VFAM;S3bS0G3G0S0G2S2S0SdS13R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2a_ok 300%nat cps_b NP cutsS2a exitsS2a (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS2a_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS2a_ok (etriple segs) (famE cutsS2a tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CMEMCPYR_E (reenterE cutsS2a tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsS2a tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (S2b_E T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp tp0' => rightE cutsS2a tp0 _ _ _ tp0' (Z.le_refl _) (CONT_cf_E rho tp tp0))
           (fun rho tp b tp0' HL Hb => rightE cutsS2a tp0 _ _ b tp0' Hb (epiS_RP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma S1_E : ltac2:(tb__ "0|4|
SdS13S2S1S21S24A2M0S23S3S2eQ40A1A1M1G1S44S1S1S1SdS13A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS13R7R6A4R5A4R4A4S49A3S3aS37R6R4A3S54S12S2fS12VJAv;R8A1R9R5R4A5VFAM;S3bS0G3G0S0G2S2S0SdS13R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS1_ok 300%nat cps_s NP cutsS1 exitsS1 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS1_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS1_ok (etriple segs) (famE cutsS1 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHF_E (reenterE cutsS1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsS1 tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (S2a_E T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL Hb => rightE cutsS1 tp0 _ _ b tp0' (Z.lt_le_incl _ _ Hb) (KDISP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem epiS_E : ltac2:(tb__ "0|2|
S23S3S2eQ40A1A1M0G0S38R3A1S54S12S2fS12VJAv;S5fA1Sc6R4R3A5VFAM;S3bS0S1S1SdS13A2M1S2A2S1S21S24A2S0G1S2S0SdS13Sc6S5fA4U0A4S0S21S24Z18fS97A4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (S1_E K_after0 nd_s0 0%nat (399, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Existence.
End Sum.
