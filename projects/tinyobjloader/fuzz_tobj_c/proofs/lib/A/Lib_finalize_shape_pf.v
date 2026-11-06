(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "sprop_eqb"; "SPUle"; "SLit"; "ss_next"; "sobj"; "SAlu"; "holds"; "ss_objs"; "sv_eqb"; "SVar"; "obj_range"; "soff"; "SPBranch"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "obj_wf"; "rw"; "cell"; "mkObj"; "odefault"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "pair"; "app"; "cons"; "nil"; "Some"; "S"; "false"; "andb"; "option"; "fst"; "nat"; "None"; "snd"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "add"; "pow"; "lt"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "AHead"; "NDA"; "am_subst"; "amode"; "nd_tv"; "JA_pre"; "tvinA"; "emeasA"; "nd_below"; "am_eqb"; "TPA"; "ffinA"; "frinA"; "nd_bd"; "nd_fr"; "fbinA"; "ANone"; "JA"; "JLA"; "nd_am"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "BXok_d"; "bd_subst"; "bxt"; "bd_below"; "bd_wpos"; "AMin"; "aval"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape"; "NP"; "vB"; "vdesc"; "vd_c"; "vd_k"; "kb"; "two47"; "sh_c"; "B32"; "ndTz"; "CHfrom"; "cs0"; "ndE"; "tv0"; "Pre_vf"; "cutsE"; "z0"; "CHf"; "Pre_ad"; "sh_k"; "vHq"; "Xk_vf"; "fins"; "nd1"; "s_gh"; "vd_el"; "C_1"; "PD_vp"; "Pre_ms"; "X_N0"; "Xk_fin"; "Xof"; "nd_fail_f"; "s_m"; "L_ms"; "PD_vf"; "Pre_m"; "Pre_vp"; "go_facts"; "mid_obj"; "s_ma"; "vAL"; "vAR"; "vd_off"; "E_m"; "P_fail"; "P_failz"; "P_nop"; "P_ok"; "Pre_fs"; "R_m"; "bd_push"; "bofs"; "finK"; "finV"; "hole_obj"; "nd0"; "ndO"; "ndPf"; "ndS"; "ndTf"; "ndTok"; "nd_nop"; "nd_ok"; "slotx"; "vHa"; "vHv"; "vLC"; "vLI"; "vPI"; "vd_d"; "xf_back_fin"; "xf_back_vfk"; "E_ad1_0"; "E_ad2_0"; "E_ad3_0"; "E_ad4_0"; "E_mg0"; "E_mk0"; "E_vf5_0"; "E_vf6_0"; "E_vf7_0"; "E_vp0"; "FL_50"; "FL_51"; "FL_60"; "FL_61"; "FL_70"; "FL_71"; "FL_E0"; "FL_E1"; "FL_p0"; "FL_p1"; "X_fit"; "X_nofit"; "X_nohead"; "X_nzret"; "X_open0"; "X_sret"; "cutsN"; "eC"; "exitsE"; "exitsN"; "ghZ"; "nd2"; "nd3"; "nd4"; "nd5"; "nd6"; "nd7"; "nd8"; "ndMok"; "ndPg"; "ndPk"; "ndZ"; "qHD"; "vSH"; "xf_back_vf"; "xf_call"; "xf_mback"; "xf_mcall"; "xf_vfcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape_pf"; "P0_fs"; "fr_obj"; "fr_xr"; "lit_in"; "boff"; "img_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Lists.ListDef"; "Forall";
"map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape_pf.Sum"; "JLf"; "Posts_fs"; "keptF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape_pf.VPP"; "P0_vp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "ulink"; "J_alloc_pre"; "Posts_malloc"; "JL_pure"; "J_memset_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_finalize_shape_eqs"; "hVP"; "isub_vf"; "isub_ad"; "holeZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "import_tv"; "tvd"; "tv_sub_eqb"; "T_ok"; "FBx"; "tnz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "robjs_checkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "PostsC"; "T_afterA3"; "FFx"; "pclMA"; "pd_okA"; "pdescA"; "xrs_inclb"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VF"; "tv_vf"; "P_fail"; "P_ok"; "P_zero"; "am_vf"; "vHDn"; "vHDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.AD"; "tv0"; "P_fail"; "P_ok"; "CH"; "ahd"; "am_np"; "am_ok"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VP"; "ndp0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape_pf.ADP"; "PD_ad"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape_pf.Sum.X"; "slotF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "PDh"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "payA"; "T_afterA"; "cmaddrA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "xrs_ok47"; "e32"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape_pf.VFP"; "P0_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape_pf.VFZ"; "CHz"; "nd0z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ef.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_finalize_shape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_finalize_shape_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_finalize_shape_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module VFZ. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_vec_finalizeZ. End VFZ.
Import RA.ReallocAddr AA.AAAddr AD.ADAddr VP.VPAddr VF.VFAddr FSAddr.
Module ADP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf. End ADP.
Module VPP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_vec_push_pf. End VPP.
Module VFP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_vec_finalize_pf. End VFP.

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  repeat match goal with |- context [bv_unsigned (eval ?r z0)] => change (bv_unsigned (eval r z0)) with (uval r (SLit 0)); rewrite (uval_lit r 0) by lia end; lia.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S22S45S0S8S3S0S4eS2bS2aS22S45A2S2aS0S7A2S2bS22S45R4R3A4S2bS0S7R2S7aA4A4R1A2S40R2S42Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros T nd r rho. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho z0)) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

Lemma edesc_eq3 : ltac2:(tb__ "0|2|
S22S22S45S45S2aS0S7A2M0G0S3S2aS2aS22S45A2M1G0A2S2bG1G0S2bS22S45R6R4A4R2A4S2bG1G0S2bS22S45R5R3A4R1A4A3S4S3S22R7R6A3S4S3S45R5R4A3S3G0R3R2A3A2A2F_;Fc';Fc;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' c c' H. injection H as E1 E2 E3. subst. auto. Qed.
Lemma edesc_eq2 : ltac2:(tb__ "0|0|
S22S22S45S45S3S2aS22S45A2S2bS22S45R4R2A4S2bS22S45R3R1A4A3S4S3S22R5R4A3S3S45R3R2A3A2F_;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' H. injection H as E1 E2. subst. auto. Qed.

Definition P0_fs (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S4S139VFF;S3eQ40M0S1dVr;PcA2A2Z518A3S139VFF;S3eG0S1dVr;P64A2A2Z30A3A2").

Definition lit_in (lo hi : sv) (n : Z) : bool := ltac2:(tb__ "0|6|
S7S28Llo;Vlo;S0S7S28Lhi;Vhi;S0S32S32S44Z0R2A2S44R2R1A2A2S44R1Vn;A2A2Lh;S1S31Li;M0Sf8S7S7S31Lb;La;M1Lop;M2G2Sf9G1Lop;M3G3S28S2S7S31La;Lw;Lsgn;M4S1S7S0S31Lk;Li;M5Ll0;X7x8Ll;G0G2G2G3G3G4S1G5Ll;X7x8").
Definition fr_obj (o : sobj) : bool := ltac2:(tb__ "0|3|
S38S32S13S19Vo;A1M0S6bA2SecS1bVo;A1M1S1aVo;A1M2Z518A3A2S32S13G0S93A2SecG1G2Z30A3A2A2").

Definition boff (e : sv) : option Z := ltac2:(tb__ "0|b|
S28S33S0A1M0L_;M1S13Ve;S6bA2S2fS0Z0A2S7G0Le;Ve;S0S36S0A1M2Lz;S1G2Li;M3Sf8S7S7Sf8G0Lop;R3S7G0Lb;R1S0G1S13R3S6bA2S2fS0R1A2G2X28x2Lk;G3Sf8S7S7G2Lb0;La;M4Lop0;M5G5Sf9G4Lop0;M6G6S28S2S7G2La;Lw;Lsgn;M7S1S7S0G2Lk;Li;Ll;M8X7x8G2G2G2G2G2G2G2G2G2Xf8xaLb;Le1;Lop;Sf8S7S7G2Lb;La;M9Lop;Sf9G9Lop;MaGaG7G8X7x8X28x2").
Definition fr_xr (r : sv * sv) : bool := ltac2:(tb__ "0|6|
S7S28Lx;S37S7S7Vr;A3S0S33S0A1S28Lx;SedS34S7S7Vr;A3M0A1S0S32S32S44Z0M1R1A2M2S44G1R2A2A2S44S41R1R2A2Z518A2A2Lk;S32S32S13G0S93A2G2A2S44R1Z30A2A2X33x2Ln;S1S31Li;Sf8S7S7S31Lb;La;M3Lop;M4G4Sf9G3Lop;M5G5S28S2S7S31La;Lw;Lsgn;S1S7S0S31Lk;Li;Ll;X7x8").
Lemma boff_sound : ltac2:(tb__ "0|0|
S8S7S0S3S33S0A1SedR2A1S2fS0R1A2A3S4S3fZ0R2A2S3fR2Z518A2A2S3fS5dR5S6bA2S70A2S3S0S5dR6R5A2S41S5dR6S6bA2R4A2A3F_;F_;F_;Fk;Fe;Frho;").
Proof.
  intros rho e k H Hk Hb. unfold two47, RA.two47 in Hb. unfold boff in H.
  destruct (sv_eqb e vB) eqn:E0.
  - apply sv_eqb_sound in E0. subst e. injection H as <-. lia.
  - destruct e as [| |op e1 e2| | | | |]; try discriminate. destruct op; try discriminate. destruct e2 as [|z| | | | | |]; try discriminate.
    destruct (sv_eqb e1 vB) eqn:E1; [|discriminate]. apply sv_eqb_sound in E1. subst e1. injection H as <-.
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition img_obj (o : sobj) : bool := ltac2:(tb__ "0|8|
S32S13S19Vo;A1SdZ0M0A1A2S7S28Lx;M1S1bVo;A1S0G1S1aVo;A1S0S32S32S44G0R2A2S44R2R1A2A2S44R1S13aA2A2Lh;S1S31Li;M2Sf8S7S7S31Lb;La;M3Lop;M4G4Sf9G3Lop;M5G5S28S2S7S31La;Lw;Lsgn;M6S1S7S0S31Lk;Li;M7Ll0;X7x8Ll;G2G4G4G5G5G6S1G7Ll;X7x8A2").

Lemma lit_in_sound : ltac2:(tb__ "0|2|
S8S7S7S7S0S0S27S1eA1S20S43R4S42Z2Z3eA2A2S3S28SecR7R6R5A3S29A3S4S3fS34S0S0S15RaS1fR9R8R7R4R3A5A2M0A3R5A2S43R5S37S0S0G0A3A2A2S4S3fS5dRbRaA2M1R6A2S43R6S41G1R7A2A2A2F_;F_;F_;Fdflt;Fcells;Fa;Fn;Fhi;Flo;Fbase;Frho;").
Proof.
  intros rho base lo hi n a cells dflt Hn H Hr. unfold lit_in in H.
  destruct lo as [l| | | | | | |]; try discriminate. destruct hi as [h| | | | | | |]; try discriminate.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite (soff_lit_small rho l), (soff_lit_small rho h) in Hr by lia. unfold uval. lia.
Qed.
Lemma img_obj_sound : ltac2:(tb__ "0|1|
S8SfS0S3S28SeeR2A1S29A3S4S3fS34S0S0S15R4R3A2M0A3R2A2S43R2S37S0S0G0A3A2A2S4S3fZ0R3A2S43R3S13aA2A2F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho [base lo hi cells dflt] a H Hr. unfold img_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply andb_prop in H as [Hb H].
  apply sv_eqb_sound in Hb. subst base.
  destruct lo as [l| | | | | | |]; try discriminate. destruct hi as [h| | | | | | |]; try discriminate.
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H1 H3]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr. unfold IMG_HI in *.
  rewrite (soff_lit_small rho l), (soff_lit_small rho h) in Hr by lia. rewrite U_lit in Hr. change (0 mod M64v) with 0 in Hr. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sf0S8S27S3dQ40A1A1Sf3OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S110S39VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S15dVCST;R1A2S4S3fZ0R2A2S43R2S13aA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S15dVXGL;R1A2S4S3fZ0R2A2S43R2S13aA2A2F_;Fa;").
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S27S2aS2aS0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JLf (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S59VAInv;VCST;VXGL;VKc;Se9VFB;VFF;A2VFB;VFF;VBX;S46Vnd;Aa").
Definition Posts_fs : list (axst * jpostA) := ltac2:(tb__ "0|2|
S2dS2aS22Se4A2M0S2bS22Se4S99SfbSa8A1A4S2dG0S2bS22Se4S9aSfbSa9A1A4S2dG0S2bS22Se4S97SfbS8aA1M1A4S2dG0S2bS22Se4S98G1A4S2eG0A1A3A3A3A3").
Definition PD_fs : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2dS2aS22S45A2M0S2bS22S45S99Sa8A4S2dG0S2bS22S45S9aSa9A4S2dG0S2bS22S45S97S8aA4S2dG0S2bS22S45S98S8aA4S2eG0A1A3A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S58VAInv;VCST;VXGL;S6aVKc;Vrho0;Se9VFB;VFF;A2VFB;VFF;VBX;S46Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2aS22S45A2S159Fn;") := ltac2:(tb__ "0|0|
S5bVAInv;VCST;VXGL;S6aVKc;Vrho0;Se9VFB;VFF;A2VFB;VFF;VBX;S46Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Se5S39S6aVrho0;Vtp0;SfcA5").

Lemma P0_now : ltac2:(tb__ "0|0|
S8S104S6aVrho0;R1A3Se9VFB;VFF;Vrho0;A3S4S139VFF;S5dR3S6bA2Z518A3S139VFF;S5dR3S93A2Z30A3A2F_;F_;Frho;").
Proof.
  intros rho Hav [H1 H2]. unfold uval, vB, vAL. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 100%positive eq_refl). split; [exact H1 | exact H2].
Qed.

Lemma fr_obj_pclMA : ltac2:(tb__ "0|1|
S8SfS0S27S2aS0S0A2A1S104S6aVrho0;R4A3Se9VFB;VFF;Vrho0;A3S3S28SeaR5A1S29A3S4S3fS34S0S0S15R7R6A2M0A3R5A2S43R5S37S0S0G0A3A2A2S129VCST;Vrho0;R5S128VFF;R8S2eS2aS2aS7S0A2S7A2A1A3R6A5F_;F_;F_;F_;FFBc;Fa;Fo;Frho;").
Proof.
  intros rho [base lo hi cells dflt] a FBc Hav HP0 H Hr. destruct (P0_now rho Hav HP0) as [PB PA].
  unfold fr_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hl]; apply sv_eqb_sound in Hb; subst base.
  - eapply (infrFF_pclMA CST _ FF); [exact PB | exact (lit_in_sound rho vB lo hi 1304 a cells dflt ltac:(lia) Hl Hr)].
  - eapply (infrFF_pclMA CST _ FF); [exact PA | exact (lit_in_sound rho vAL lo hi 48 a cells dflt ltac:(lia) Hl Hr)].
Qed.
Lemma fr_obj_cmaddrA : ltac2:(tb__ "0|1|
Sf0S8S33S0A1SfS0S104S6aVrho0;R4A3Se9VFB;VFF;Vrho0;A3S52VFF;R7A2S3S28SeaR5A1S29A3S4S3fS34S0S0S15R8R6A2M0A3R5A2S43R5S37S0S0G0A3A2A2S14eVCST;RaR8R6A4F_;F_;F_;F_;F_;Fa;Fo;Fxo;Frho;FAi;").
Proof.
  intros Ai rho xo [base lo hi cells dflt] a Hav HP0 HFF H Hr. destruct (P0_now rho Hav HP0) as [PB PA].
  unfold fr_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hl]; apply sv_eqb_sound in Hb; subst base.
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PB | exact (lit_in_sound rho vB lo hi 1304 a cells dflt ltac:(lia) Hl Hr)].
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PA | exact (lit_in_sound rho vAL lo hi 48 a cells dflt ltac:(lia) Hl Hr)].
Qed.
Lemma fr_xr_pclMA : ltac2:(tb__ "0|1|
S8S2aS7S7A2S0S27S2aS0S0A2A1S104S6aVrho0;R4A3Se9VFB;VFF;Vrho0;A3S3fS5dR6S6bA2S70A2S3S28SebR6A1S29A3S4S3fS5dR8S34S7S7R7A3A2M0R6A2S43R6S41G0S5dR8S37S7S7R7A3A2A2A2A2S129VCST;Vrho0;R6S128VFF;R9S2eS2aS2aS7S0A2S7A2A1A3R7A5F_;F_;F_;F_;F_;FFBc;Fa;Fr;Frho;").
Proof.
  intros rho [rb rn] a FBc Hav HP0 Hb H Ha. destruct (P0_now rho Hav HP0) as [PB PA].
  unfold fr_xr in H. cbn [fst snd] in H, Ha. destruct rn as [|n| | | | | |]; try discriminate.
  destruct (boff rb) as [k|] eqn:EB.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    rewrite uval_lit in Ha by lia. rewrite (boff_sound rho rb k EB ltac:(lia) Hb) in Ha. eapply (infrFF_pclMA CST _ FF); [exact PB | lia].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. subst rb.
    apply Z.leb_le in H2. apply Z.leb_le in H3. rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST _ FF); [exact PA | lia].
Qed.

Lemma d_live : ltac2:(tb__ "0|0|
S45S8S27S3dQ40A1A1S27Sf4A1Sf3S7S0S7S7VJAv;R9R8R7R6R5A5S67S2aS7S7A2S2bS7S7R5S6fR4R2A2A4S4bRaA1A3S4S3fZ1R5A2S3fR5Z80A2A2S3fS5dRbR4A2S72A2S3fS5dRcR6A2S5dRcR5A2A2S6S3S0S5dRdR7A2Z0A3A1S122ReS2bS7S7RaS6fR9R7A2A4A2F_;F_;F_;F_;F_;F_;Fk;Fc;Fe;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md d e c k HJ Hin He Hk Hck Hc Hd.
  pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue nd rho tp tr md (d, kb e k) HJ Hin Hd) as Z0.
  cbn [snd] in Z0. change (bv_unsigned (eval rho (kb e k))) with (uval rho (kb e k)) in Z0.
  unfold kb, B32, Lib_vec_reserve.B32 in *. pose proof (uval_range rho k). pose proof (uval_range rho c). rewrite uval_mul_lit in Z0 by nia. assert (uval rho k = 0) by nia. lia.
Qed.

Lemma JA_tv_swap : ltac2:(tb__ "0|2|
S27S2aS7S7A2M0A1G0G0S27S2aS2aS7S0A2S7A2A1S27S5eA1S4aS8S27S3dQ40A1A1S27Sf4A1Sf3VJAv;S48S2cG0RaS2dG0R9S2dG0R8S2eG0A1M1A3A3A3R7R6R5A4R4R3R2R1A5VJAv;S48S2cG0RbS2dG0R9S2dG0RaG1A3A3A3R8R7R6A4R5R4R3R2A5F_;Fmd;Ftr;Ftp;Frho;Fam;Fbd;Ffr;Fy;Fx;Fl;").
Proof.
  intros l x y fr bd am rho tp tr md (Ai & kc & HJ). exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU |- *.
  assert (PERM : forall t, In t (l ++ [y; x]) <-> In t (l ++ [x; y])).
  { intros t. rewrite !in_app_iff. cbn. tauto. }
  assert (HCNT : cntS rho (l ++ [x; y]) <= cntS rho (l ++ [y; x])) by (rewrite !cntS_app, !cntS_cons; lia).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|exact (JA_tail_le _ _ _ rho rho _ _ HCNT HPA)]]]]]].
  - split; [|split].
    + unfold tvinA in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). apply PERM. exact Ht.
    + cbn [nd_tv]. pose proof (tvd_app_l rho _ _ HD) as D1. pose proof (tvd_app_r rho _ _ HD) as D2. pose proof (tvd_app_cross rho l [x; y]) as D3.
      apply tvd_app; [exact D1 | |].
      * cbn in D2 |- *. destruct D2 as [Dxy _]. split; [|split; [intros t' [] | exact I]].
        intros t' [<-|[]] Hy Hx E0. apply (Dxy y ltac:(left; reflexivity) Hx Hy). symmetry. exact E0.
      * intros t t' Ht Ht' Hnz Hnz'. apply (D3 t t' HD Ht); [cbn in Ht' |- *; tauto | exact Hnz | exact Hnz'].
    + unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply PERM. exact Ht.
  - unfold XA in *. eapply (proj1 (XAz_transport FB FB _ Ai Ai (rm rho) (rm rho) (tvals rho (l ++ [x; y])) (tvals rho (l ++ [y; x])) kc HXA _ _ _ _)).
    Unshelve.
    + intros b n Hin Hnf Hut. split; [exact Hin|]. split; [exact Hnf|]. intros v Hv. apply Hut. unfold tvals in *. apply in_map_iff in Hv as (t & <- & Ht). apply in_map. apply PERM. exact Ht.
    + intros; reflexivity.
    + intros; split; [reflexivity | auto].
    +
      intros bn H1 _ H3 H4. split; [exact H1|]. split; [exact H3|]. intros v Hv. apply H4. unfold tvals in *. apply in_map_iff in Hv as (t & <- & Ht). apply in_map. apply PERM. exact Ht.
Qed.
Lemma SPA_tv_swap : ltac2:(tb__ "0|2|
S27S2aS7S7A2M0A1G0G0S27S2aS2aS7S0A2S7A2A1S27S5eA1S4aS22S8S27S3dQ40A1A1S101S3aS39VJAv;S48S2cG0RaS2dG0R9S2dG0R8S2eG0A1M1A3A3A3R7R6R5A4A1R4R3R2R1A6S3aS39VJAv;S48S2cG0RbS2dG0R9S2dG0RaG1A3A3A3R8R7R6A4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ffr;Fy;Fx;Fl;").
Proof. intros l x y fr bd am A rho tp [tr [ms md]] [Hsm HJ]. split; [exact Hsm|]. apply JA_tv_swap. exact HJ. Qed.

Lemma eC_val : ltac2:(tb__ "0|1|
S8S6cS7S4S3fZ1S83R2A1M0A2S3fG0Z80A2A2S3fS5dR4R2A2S72A2S3S0S5dR5SceR4R3A2A2S40S83R4A1S5dR5R3A2A2A3F_;F_;Fc;Fv;Frho;").
Proof.
  intros rho v c He Hc. unfold eC, B32, Lib_vec_reserve.B32 in *. pose proof (uval_range rho c).
  apply uval_mul_lit; nia.
Qed.

Lemma amin1_rng : ltac2:(tb__ "0|3|
S8S7S4S3fZ0M0S65R2S64R1Z1M1G0G1A4A2M2A2S3fG2G1A2A2Fe;Fr;").
Proof. intros r e. cbn [aval]. lia. Qed.
Lemma pay_fin : ltac2:(tb__ "0|3|
S35S6cS27S9A1S27S5eA1S3S33S6cA1S68S6cS80R4A3S2fS6cR3A2A3S3S28S63R2A1S29A3S3S28S66S9SbScS6dR5A1S6eR5A1A2A1R4A3S29A3S3S28S66S9SbScS6eR6A1SdS72A1A2A1R5A3S29A3S14cS6aVrho0;Se9VFB;VFF;A2R6SdZ0M0A1G0S2cS5eS2dS5eSa0R8A1S2dS5eS9fR8A1S2eS5eA1M1A3A3R5A3S2cS5eS7bR7S6dR7A1A2S2cS5eS2dS5eSa0S30R8A1M2A1S2dS5eS9fG2A1G1A3A3R5A3A3A8F_;F_;F_;F_;Frest;Ffacts;Fv;Fj;").
Proof.
  intros j v facts rest Hj HW H1 H2.
  split; [unfold bd_wpos in *; rewrite !forallb_app, HW; unfold CHf; destruct (vd_mesh v); reflexivity|]. split; [lia|].
  intros r HF _ _ HNN. unfold pay_sem. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in F1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in F2.
  unfold B32, Lib_vec_reserve.B32 in F2. rewrite uval_lit in F2 by lia.
  apply bd_nn_app in HNN as [HN1 HNR].
  pose proof (uval_range r mi_c) as R1. pose proof (uval_range r fv_c) as R2. pose proof (uval_range r mm_c) as R3. pose proof (uval_range r sg_c) as R4.
  pose proof (uval_range r li_c) as R5. pose proof (uval_range r lc_c) as R6. pose proof (uval_range r pi_c) as R7.
  pose proof (amin1_rng r mi_c) as M1. pose proof (amin1_rng r fv_c) as M2. pose proof (amin1_rng r mm_c) as M3. pose proof (amin1_rng r sg_c) as M4.
  destruct j as [|[|[|[|[|[|[|j]]]]]]].
  8: { cbn in Hj. destruct j; discriminate. }
  all: cbn in Hj; injection Hj as <-; cbn [vd_c vd_k vd_el vMI vFV vMM vSG vLI vLC vPI] in F1, F2;
    (lazymatch goal with |- context [CHf ?w _] =>
       pose proof (eC_val r w (vd_c w) ltac:(cbn; lia) ltac:(unfold B32, Lib_vec_reserve.B32; cbn [vd_c vd_k vMI vFV vMM vSG vLI vLC vPI]; lia)) as EV end;
     cbn [vd_el vd_c vMI vFV vMM vSG vLI vLC vPI] in EV);
    rewrite !bsumV_app, !bsumK_app; unfold finV, finK, CHf, AMin1; cbn -[uval aval Z.mul Z.add Z.sub Z.of_nat]; unfold bival; cbn -[uval aval Z.mul Z.add Z.sub];
    repeat match goal with |- context [aval ?rr (ASv ?e)] => change (aval rr (ASv e)) with (uval rr e) end; rewrite EV;
    (split; [lia|]); (split; [lia|]);
    unfold bd_nn in *; repeat (apply Forall_cons; [unfold bival; cbn -[uval aval Z.mul Z.add Z.sub];
                                                   repeat match goal with |- context [aval ?rr (ASv ?e)] => change (aval rr (ASv e)) with (uval rr e) end; rewrite ?EV; lia|]); exact HNR.
Qed.

Definition keptF : list (sv * sv) := ltac2:(tb__ "0|1|
S2cS2aS7S7A2M0Sf6S6cG0S89S80A4S2dG0S89SdeA1S2eG0A1A3A3").
Definition keptP : list (sv * sv) := ltac2:(tb__ "0|1|
S2cS2aS7S7A2M0Sf6S6cG0S89S80A4S2dG0S2bS7S7S94SdZ40A1A4S2eG0A1A3A3").

Lemma tvx_app_l : ltac2:(tb__ "0|2|
Sf0S8S27S2aS7S7A2M0A1M1G1S4dVFB;R4R3S2cG0R2R1A3A4S11eR4S2cG0R3R2A3A2S11cR5S2cG0R4R3A3A2S4S4dVFB;R7R6R5A4S4S11eR6R5A2S11cR6R5A2A2A2F_;F_;F_;Fl2;Fl1;Frho;FAi;").
Proof.
  intros Ai rho l1 l2 HN HD HZ. unfold tvinA, tvz in *. apply Forall_app in HN as [HN _]. apply Forall_app in HZ as [HZ _].
  split; [exact HN|]. split; [exact (tvd_app_l rho l1 l2 HD) | exact HZ].
Qed.

Lemma b47_of : ltac2:(tb__ "0|0|
S8S27S9A1Sf5S9S11R2A1R1A3S3S28S66S9SbScS6bSdS70A1A2A1R2A3S29A3S3fS5dR4S6bA2S70A2F_;F_;FF;Frho;").
Proof. intros rho F HF H. pose proof (holds_mem _ _ _ HF H) as X. zf X. unfold two47, RA.two47 in *. rewrite uval_lit in X by lia. exact X. Qed.

Lemma site_client : ltac2:(tb__ "0|4|
S22S27SfA1S27S2aS7S7A2A1M0G0S8Sf0S8S27S3dQ40A1A1Sf3VAInv;R4R3R2R1A4Sf5S9S11R6A1SaS23RaA1A1A3Se9VFB;VFF;Vrho0;A3S104S6aVrho0;R8A3S51Vrho0;R8A2S120RaSf2Sf1R9A1A1A2S4dVFB;RaRbRcA4S11eRcRdA2S11cRdReA2S53VFF;RdReS2eS2aS2aS7S0A2S7A2A1M1A4S3S28S66S9SbScS6bSdS70A1A2A1SaS23R13A1A1A3S29A3S3S28S12fSaS23R14A1A1R11G1S36S35A1M2SeaR13A6S29A3S3S28S123VXGL;SaS23R15A1M3A1R12G1G2S12G3A1SebR13A8S29A3S4S12dVCST;Vrho0;VFB;VFF;R12R13G1R15A8S12eVCST;VXGL;Vrho0;VFB;VFF;R12R13G1R14A9A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Frho;Fkept;FXk;FR;FE;").
Proof.
  intros E R Xk kept rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR H47 HR HX. pose proof (b47_of rho _ HF H47) as Hb. split.
  - intros o a Ho Hr.
    exact (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ kept [] None fr_obj R rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR HR
             (fun o' a' Ho' HE Hr' => fr_obj_pclMA rho o' a' _ Hav HP0 HE Hr') o a Ho Hr).
  - intros r a Hr Ha.
    exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho _ kept [] None (ss_objs (ax_S E)) fr_xr Xk rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR HX
             (fun r' a' Hr' HE Ha' => or_introl (fr_xr_pclMA rho r' a' _ Hav HP0 Hb HE Ha')) r a Hr Ha).
Qed.

Lemma site_rt : ltac2:(tb__ "0|4|
S22S27SfA1S27S2aS7S7A2A1S8Sf0S8S27S3dQ40A1A1Sf3VAInv;R4R3R2R1A4Sf5S9S11R6A1SaS23R9A1A1A3Se9VFB;VFF;Vrho0;A3S104S6aVrho0;R8A3S51Vrho0;R8A2S120RaSf2Sf1R9A1A1A2S56VFB;RaA2S52VFF;RbA2S4dVFB;RcRdReA4S11eReRfA2S11cRfR10A2S53VFF;RfR10S2eS2aS2aS7S0A2S7A2A1M0A4S3S28S66S9SbScS6bSdS70A1A2A1SaS23R14A1A1A3S29A3S3S28S12fSaS23R15A1A1R13G0S36S35A1M1SeaR14A6S29A3S3S28S123VXGL;SaS23R16A1M2A1R14G0G1S12G2A1SebS24R16A1A8S29A3S4S14fVCST;R13S36S0A1M3R14R16A5S151VCST;VXGL;R13G3R14S24R17A1A6A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Frho;Ftv;FR;FE;").
Proof.
  intros E R tv rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HBf HFF HN HD HZ HFR H47 HR HX. pose proof (b47_of rho _ HF H47) as Hb. split.
  - exact (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho _ tv [] None fr_obj R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR HR
             (fun o' a' Ho' HE Hr' => fr_obj_pclMA rho o' a' _ Hav HP0 HE Hr')).
  - exact (proj1 (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho _ tv [] None (ss_objs (ax_S E)) fr_xr (ax_X E) rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR HX
             (fun r' a' Hr' HE Ha' => or_introl (fr_xr_pclMA rho r' a' _ Hav HP0 Hb HE Ha')))).
Qed.

Lemma block_pclMA : ltac2:(tb__ "0|2|
Sf0S8S27S2aS7S7A2M0A1G0S0S4dVFB;R5R4R3A4S11cR5R4A2S67G0R4R5A3S4S3fS5dR7S34S7S7R5A3A2M1R4A2S43R4S41G1S5dR7S37S7S7R5A3A2A2A2A2S8S129VCST;R1S121VFB;R9R8A3S128VFF;R9S2eS2aS2aS7S0A2S7A2A1A3R6A5Fr0;F_;F_;F_;F_;Fa;Ft;Fkept;Frho;FAi;").
Proof.
  intros Ai rho kept t a HN HZ Hin Ha r0.
  destruct (Z.eq_dec (uval rho (fst t)) 0) as [Hz|Hnz].
  - exfalso. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [snd] in X.
    specialize (X ltac:(intros Y; apply Y; exact Hz)). unfold uval in Ha. lia.
  - right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split.
    + apply In_FBx. right. exists t. split; [exact Hin|]. split; [exact Hnz | symmetry; apply surjective_pairing].
    + unfold tvv. cbn [fst snd]. unfold uval in Ha. exact Ha.
Qed.

Lemma go_holds : ltac2:(tb__ "0|1|
S45S8S27S3dQ40A1A1S27Sf4A1Sf3S6cS27S9A1VJAv;R7R6R5R4R3A5S67S2aS7S7A2S89R3A1S4bR8A1A3S4S3fZ1S83R4A1M0A2S3fG0Z80A2A2Sf5S9S11R9A1R4A3S3S28S66S9SbS18S17SfaS6dR6A1SdZ0A1A3A1A1R5A3S29A3S3S28S66S9SbScS6dR7A1S6eR7A1A2A1R6A3S29A3S3S28S66S9SbScS6eR8A1SdS72A1A2A1R7A3S29A3Sf5S9S11RdA1S90R9A1A3F_;F_;F_;F_;F_;F_;F_;FF;Fv;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md v F HJ Hin He HF H0 H1 H2.
  pose proof (holds_mem _ _ _ HF H0) as F0. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F0. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in F1. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in F2.
  rewrite uval_lit in F0 by lia. unfold B32, Lib_vec_reserve.B32 in F2. rewrite uval_lit in F2 by lia.
  assert (TNZ : tnz rho (Xof v)) by (apply (d_live nd rho tp tr md (vd_d v) (vd_el v) (vd_c v) (vd_k v) HJ Hin He); unfold B32, Lib_vec_reserve.B32; lia).
  pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ALA _ _ _ _ _ (Xof v) eq_refl HJ Hin TNZ) as TF.
  unfold go_facts. constructor; [|constructor; [|constructor]].
  - apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd Xof]. do 3 right. left. reflexivity.
  -
    apply (proj2 (h_ule _ _ _)). rewrite uval_lit by lia. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in F0.
    pose proof (uval_range rho (vd_c v)). unfold uval in *. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S27S9A1S27S5eA1S3S28S63R1A1S29A3S14cS6aVrho0;Se9VFB;VFF;A2R3SdZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S27S3dQ40A1A1SfeF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S3bS22S8S27S3dQ40A1A1SfeSf5S9S11R3A1SaS23R4A1A1A3VTR;S3aS39R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SfeSfeSfeS101R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S3bS3bS22S22S119S27SfA1M0S27S2aS22Se4A2M1A1S27S2aS7S7A2M2A1SfeS8S27S3dQ40A1A1M3G2S67G2R1R5A3S67G2R2S24RbA1A3F_;Fr;S3S33G0A1Se7RaR9R8A3S2fG0R7A2A3S3S28Se6RbRaR9R8Sf6G1S22S34S22Se4A2R7A4A5S29A3S8G3VTR;S3aS39RfRdR2R1A5Se5S39SeS23RdA1A1R2R1RaA5A2Ftp1;Frho1;S27Sf4A1M4S131Sf3S3cS39R9R8R10S2bG4S13bR3S13cR2R1A2A4A5R13RaR9R4R2A4R13S118S117RbRfS11bR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S22Se4G4S131Sf3S8G3G4S131Sf3S67G1S2bS22Se4RaR9A4R14A3S3cS39R12R11R19S2bG4S13bR9S13cR8R7A2A4A5R1cR13R12RaR8A4S104SeS23R1aA1A1S118S117R14R18S11bR9R13RaA3A3R19A2R8A3S3cS39R9R8ReS2bG4S13bR7S13cR6R5A2A4A5ReS118S117R16R1aS11bRbR15RcA3A3R1bA2R15RaR9R8R6A6S4S15eR17S11bRcR16RdA3R1bR1cR1dR10R1eR19RbA9S8S106R18S11bRdR17ReA3R1cR1dS23R1eA1S23R1fA1S23R11A1R1RcA9VTR;S3aS39Se8R11S118S117R19R1dS11bReR18RfA3A3R1eA2R18RdRcA5S15fR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S3aS39R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CAD : ltac2:(tb__ "0|1|
S27S2aS0S0A2M0A1S27S2aG0S0A2A1S61S8S27S3dQ40A1A1S5fZ3R3A2VTR;S3aS39S4cVAInv;VCST;VXGL;VKc;S147VCST;R6R5A3R6R5R4S46S144AaS7cR3R2A5Se5S39SefR3R2S126VAInv;VCST;VXGL;VKc;S147VCST;A1S46S146R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CVF : ltac2:(tb__ "0|1|
S27S2aS0S0A2M0A1S27S2aG0S0A2A1S61S8S27S3dQ40A1A1S5fZ4R3A2VTR;S3aS39S4cVAInv;VCST;VXGL;VKc;S155VCST;R6R5A3R6R5R4S46S157AaS78R3R2A5Se5S39SefR3R2S126VAInv;VCST;VXGL;VKc;S155VCST;A1S46S8dR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CVP : ltac2:(tb__ "0|1|
S27S2aS0S0A2M0A1S27S2aG0S0A2A1S61S8S27S3dQ40A1A1S5fZ4R3A2VTR;S3aS39S4cVAInv;VCST;VXGL;VKc;S103R6R5A2R6R5R4S46S14aS112S29S145A3AaS8fR3R2A5Se5S39SefR3R2S126VAInv;VCST;VXGL;VKc;S103S46S149S85S112S29A3R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
Sf0S8S27S3dQ40A1A1VTR;S3aS39S10dVAInv;R3VKc;A3S86R2R1A5Se5S39SefR2R1S2dS2aS22Se4A2M0S2bS22Se4S8cS10cVAInv;VCST;VXGL;R3VKc;A5A4S2eG0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sf0S8S27S3dQ40A1A1VTR;S3aS39S10aVAInv;S2eS109A1M0S107R3VKc;S14PcA1A6S8eR2R1A5Se5S39SefR2R1S10bS108VAInv;VCST;VXGL;G0S107R3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S22S45S2aS0S7A2M0S8S27S3dQ40A1A1M1S0G1S67S2aS2aS22S45A2M2G0A2S2bG2G0S2bS22S45R7R6A4R5A4S79A3S4S3fZ0S4eS2bG2G0S2bS22S45R8R7A4R6A4R5A2M3A2S43G3R3A2A2VTR;S3aS39VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S22S45S8S27S3dQ40A1A1M0S0G0S67S2aS22Se4A2S2bS22Se4R6SfbR5A1A4SfcA3VTR;S3aS39VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Hypothesis NAMEBLK : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0SfeS8G0VTR;S3aS39VJAv;S81A1S84R2R1A5R3A2Ftp';Frho';S22S45S8G0S67S2aS22Se4A2S2bS22Se4R4SfbR3A1A4SfcA3VTR;S3aS39VJAv;R4A1R5R3R2A5R7A2F_;Ftp';Frho';Fnd;FP;VTR;S3aS39VJAv;S76A1S87R5R4A5R3A2F_;F_;FQ';Ftp;Frho;").

Variable FAMN : Z -> assn.
Hypothesis REENTER_N : ltac2:(tb__ "0|3|
S22S45S2aS0S7A2M0S8S27S3dQ40A1A1S0S67S2aS2aS22S45A2M1G0A2S2bG1G0S2bS22S45R6R5A4R4A4ScdA3S4S3fZ0S4eS2bG1G0S2bS22S45R7R6A4R5A4R4A2M2A2S43G2R2A2A2VTR;S3aS39VJAv;R7A1R8R5R4A5VFAMN;R3A1A2F_;F_;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis C1OUT : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0VTR;S3aS39VJAv;S81A1S84R3R2A5VFAMN;R1A1A2Fb;Ftp;Frho;").
Hypothesis POSTN : ltac2:(tb__ "0|0|
S22S45S8S27S3dQ40A1A1S0S67S2aS22Se4A2S2bS22Se4R5SfbR4A1A4SfcA3VTR;S3aS39VJAv;R5A1R6R4R3A5VFAMN;R2A1A2F_;Fb;Ftp;Frho;Fnd;FP;").

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := do n right; left; reflexivity.

Lemma X_FIN : ltac2:(tb__ "0|16|
S35S6cS22S22S22S22S22S22S119S27SfA1M0S0S8S27S3dQ40A1A1M1S0G1S3S33S6cA1S68S6cS80RfA3S2fS6cReA2A3S3S28S69S9S21SeS23ReA1M2A1A1S2cS9S90RfA1SaG2A1A3A3S29A3S3S28S66S9SbS18S17SfaS6dR10A1SdZ0M3A1M4A3A1A1SaS23RfA1A1A3S29A3S3S28S66S9SbScS6dR11A1S6eR11A1A2A1SaS23R10A1A1A3S29A3S3S28S66S9SbScS6eR12A1SdS72A1M5A2A1SaS23R11A1A1A3S29A3S3S33S22A1M6S102S158S90R13A1R12A2Se0Z40M7A1A2S2fS22R11A2A3S3S28S66S9SbScS6dR14A1S6eR14A1A2A1SaS23R12A1A1A3S29A3S3S28S66S9SbScS6eR15A1G5A2A1SaS23R13A1A1A3S29A3S3S28S66S9SbScS6bSdS70A1A2A1SaS23R14A1A1A3S29A3S3S28S12cS88R17A1S24R15A1A2S29A3S3S33G0A1Se7R16S7cR11A3S2fG0R10A2A3S3S28Se6R17S7cR12R11Sf6S2aS22S45A2M8S22S34S22S45A2S146A4A5S29A3S3S28S14bS6aR13A2S29A3S3S28S105R14SefA2S29A3S3S28S130S6aSeS23R1aA1A1A2S29A3S3S28S4fSeS23R1bA1A1S48S2cS2aS7S7A2M9SfdS2dG9S2bS7S7S94SdG7A1A4S2eG9A1A3MaA3S2eS2aS2aS7S0A2S7A2A1MbS2cS5eS7bR1dS6dR1dA1A2S2cS5eS74S30R1eA1S75A2S9dS71S7dA2McA3A3S47S7eS29A2MdA4A2S29A3S3S28S62SeS23R1cA1A1S2cS5eS74S30R1fA1S75A2GcA3A2S29A3S3S28S11fR18GaS13dA3S29A3S3S28S50S49R19S141A2GdA2S29A3S3S28S15cSaS23R1fA1A1G4G3S2cS5eS7bR21S6dR21A1A2S2cS5eS74S30R22A1S75A2GcA3MeA3S2cS5eS60R1aS140A2GeA3A5S29A3S3S28S69S12bS12aS7cSefR1bSeS23R20A1A1A4S146A3S29A3S3S28S12fSaS23R21A1A1SfdGbS36S35A1MfSeaR1bA6S29A3S3S28S123VXGL;SaS23R22A1M10A1SfdGbGfS12G10A1SebS88R24A1A8S29A3S3S7S116R1ePdA2Sb0R25A1A3S3S7S116R1fP10A2S6fS83R26A1S6eR26A1A2A3S3S22S127S7cR25R20R1fS13fS88R27A1A6R24A3S3G6S102R25Sb1S30R29A1A1A2S2fS22R24A2A3S4S3S27G9A1M11S11dS114R27R22S13fA3M12S13dA2GaA3S3S4aS49G12S143A2S47SabS29A2A3A2S3S22S127S7cR28R23R22S13eS88R2aA1A6R25A3S3G6S102R26Sb1S30R2cA1A1A2S2fS22R25A2A3S4S3G11S11dS114R2aR25S13eA3M13S13dA2GaA3S3S4aS49G13S142A2S47S7eS31A2A3A2S67S2aG8S2aS0S7A2M14A2M15S2bG8G14S2bS22S45R29Sa7S30R2eA1SabA2A4S2bS0S7R24S7aA4A4S79A3S67G15S2bG8G14S2bS22S45R28Sa6S30R2fA1S7eA2A4S2bS0S7R25S7aA4A4S79A3S3fG3R26A2S3fS40S41R27Z1A2S42Z2G7A2A2R24A2VTR;S3aS39VJAv;S48S77GbS2cS5eS74R32S75A2GcA3GdA4A1R30R27R26A5VFAM;R25R24A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FrkT;FR;Fs;FTf;FTf0;FTok;FTok0;FE;FE0;Fv;Fj;").
Proof.
  intros j v E0 E Tok0 Tok Tf0 Tf s R rkT rho tp b tp0 Hj Hgb Hc0 Hck0 HkB0 HE Hck HkB H47 HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham Hpay Hpd HR HX Hs13 Hs16
         HTok0 HTok Himp_ok HTf0 HTf Himp_f HinOk HinF Hrk Hb.
  assert (Hv : In v fins) by (eapply nth_error_In; exact Hj).
  assert (He128 : 1 <= vd_el v <= 128) by (cbn in Hv; destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; lia).
  assert (HinX : In (Xof v) tv0) by (unfold tv0; apply in_or_app; left; apply in_map; exact Hv).

  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true))) E rho tp).
  { intros w Hw.
    assert (Hw1 : SPA segs (JAv (NDA tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k) (AHead vHq true))) (ax_add_facts (go_facts v) E0) rho tp w).
    { apply (SPA_refacts_JA segs); [exact Hw | exact Hgb |].
      intros tr md HJ HF. apply Forall_app. split; [|exact HF]. exact (go_holds _ rho tp tr md v _ HJ HinX He128 HF Hc0 Hck0 HkB0). }
    pose proof (SPA_axforms segs _ (xf_call 64) rho _ E tp w HE Hw1) as Hw2.
    apply (JA_repay segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k)
             (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true) E rho tp w); [|exact Hw2].
    exact (pay_fin j v (ss_facts (ax_S E)) (bd_push sh_c sh_k) Hj eq_refl Hck HkB). }

  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  change (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) with (CHf v (vd_c v) ++ CHfrom (S j) cs0 ++ bd_push sh_c sh_k).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX (ADP.P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad AD.nd0 ADP.PD_ad NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD eq_refl
           E s R (Xk_fin v) rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom (S j) cs0 ++ bd_push sh_c sh_k) (AHead vHq true) (FAM b tp0)
           HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). exact Hpay.
  - exact Hpd.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E R (Xk_fin v) keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR H47 HR HX) as [A B].
    split; [exact A|]. split; [exact B|].
    unfold ADP.P0_ad. intros a Ha. unfold uval, AD.vSRC, AD.vLS in Ha. cbn [eval] in Ha. rewrite !rw_call', Hs13, Hs16 in Ha.
    apply (block_pclMA Ai rho keptF (Xof v) a HN1 HZ1); [apply in_or_app; left; apply in_map; exact Hv | exact Ha].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [ADP.PD_ad In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am AD.ndF AD.ndK AD.nd0]; fold (isub_ad E s AD.P_fail); fold (isub_ad E s AD.P_ok).
    +   rewrite HTf0, (proj1 Himp_f), (proj2 Himp_f). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tf (ndTf (S j) vHq) (rkT, z0) rho'); [exact HinF | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tf0 Tf tp' w HTf Hw).
    +   rewrite HTok0, (proj1 Himp_ok), (proj2 Himp_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tok (ndTok (S j) vHa) (rkT, z0) rho'); [exact HinOk | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tok0 Tok tp' w HTok Hw).
Qed.
Lemma X_E_ad1 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z92S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;S81A1Sb3R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd1.
  apply (X_FIN 0 vMI E_ad1_0 E_ad1 T1_ok0 T1_ok T1_fail0 T1_fail s_ad1 R_ad1 145 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad1_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T1_ok0_eq | exact T1_ok_eq | exact imp_ad1_ok | exact T1_fail0_eq | exact T1_fail_eq | exact imp_ad1_fail | innth 3 | innth 4 | lia | lia].
Qed.
Lemma X_E_ad2 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z88S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;Sd2A1Sb4R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd2.
  apply (X_FIN 1 vFV E_ad2_0 E_ad2 T2_ok0 T2_ok T2_fail0 T2_fail s_ad2 R_ad2 135 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad2_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T2_ok0_eq | exact T2_ok_eq | exact imp_ad2_ok | exact T2_fail0_eq | exact T2_fail_eq | exact imp_ad2_fail | innth 6 | innth 7 | lia | lia].
Qed.
Lemma X_E_ad3 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z7eS42Z2Z40A2A2R2A2VTR;S3aS39VJAv;Sd3A1Sb5R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd3.
  apply (X_FIN 2 vMM E_ad3_0 E_ad3 T3_ok0 T3_ok T3_fail0 T3_fail s_ad3 R_ad3 125 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad3_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T3_ok0_eq | exact T3_ok_eq | exact imp_ad3_ok | exact T3_fail0_eq | exact T3_fail_eq | exact imp_ad3_fail | innth 9 | innth 10 | lia | lia].
Qed.
Lemma X_E_ad4 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z74S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;Sd4A1Sb6R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd4.
  apply (X_FIN 3 vSG E_ad4_0 E_ad4 T4_ok0 T4_ok T4_fail0 T4_fail s_ad4 R_ad4 115 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad4_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T4_ok0_eq | exact T4_ok_eq | exact imp_ad4_ok | exact T4_fail0_eq | exact T4_fail_eq | exact imp_ad4_fail | innth 12 | innth 13 | lia | lia].
Qed.

Lemma bofs_val : ltac2:(tb__ "0|0|
S8S0S3fS5dR2S6bA2S70A2S4S3fZ0R2A2S3fR2Z518A2A2S3S0S5dR4S9eR3A1A2S41S5dR4S6bA2R3A2A3F_;F_;Fk;Frho;").
Proof.
  intros rho k Hb Hk. unfold bofs, two47, RA.two47 in *. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_VF : ltac2:(tb__ "0|16|
S35S6cS35S22S22S22S22S22S22S119S27SfA1M0S0S8S27S3dQ40A1A1M1S0G1S3S33S6cA1S68S6cS80R10A3S2fS6cRfA2A3S3S33S22A1M2S102ReSe3RfS95R10A1A2A2S2fS22RdA2A3S3S28S66S9SbScS6dR11A1S6eR11A1A2A1SaS23ReA1A1A3S29A3S3S28S66S9SbScS6eR12A1SdS72A1A2A1SaS23RfA1A1A3S29A3S3S28S66S9SbScS6bSdS70A1A2A1SaS23R10A1A1A3S29A3S3S28S12cS7fR14A1S24R11A1A2S29A3S3S33G0A1Se7R12S78RdA3S2fG0RcA2A3S3S28Se6R13S78ReRdSf6S2aS22S45A2M3S22S34S22S45A2S8dA4A5S29A3S3S28S14bS6aRfA2S29A3S3S28S105R10SefA2S29A3S3S28S130S6aSeS23R16A1A1A2S29A3S3S28S4fSeS23R17A1A1S48S2cS2aS7S7A2M4SfdS2dG4S2bS7S7S94SdZ40M5A1A4S2eG4A1A3M6A3S2eS2aS2aS7S0A2S7A2A1M7S2cS5eS7bR1aS6dR1aA1A2S2cS5eS74S30R1bA1S75A2S9dS71S7dA2M8A3A3S47S7eS29A2M9A4A2S29A3S3S28S62SeS23R18A1A1S2cS5eS74S30R1cA1S75A2G8A3A2S29A3S3S28S11fR14G6S132A3S29A3S3S28S50S49R15S136A2G9A2S29A3S3S28S15cSaS23R1bA1A1SdZ0MaA1GaS2cS5eS7bR1eS6dR1eA1A2S2cS5eS74S30R1fA1S75A2G8A3MbA3S2cS5eS60R16S156A2GbA3A5S29A3S3S28S69S12bS12aS78SefR17SeS23R1cA1A1A4S8dA3S29A3S3S28S12fSaS23R1dA1A1SfdG7S36S35A1McSeaR17A6S29A3S3S28S123VXGL;SaS23R1eA1MdA1SfdG7GcS12GdA1SebS7fR21A1A8S29A3S3S7S116R1aPcA2S9eS95R22A1A1A3S3S7S116R1bPfA2Sb0R23A1A3S3S7S116R1cP11A2S6fS83R24A1S6eR24A1A2A3S4S3fGaS95R25A1MeA2S3fS41GeZ20A2Z518A2A2S3G2S102S127S78R23R1eR1dS135S7fR26A1A6SdfR25S30R27A1A2A2S2fS22R22A2A3S4S3S27G4A1MfS11dS113R24R1fS135A3M10S132A2G6A3S4S3S4aS49G10S136A2G9A3S3S27S5eA1S60G10S156A2S7bR27S6dR27A1A2A3A2A2S3S22S158S2dS9Sd1S2eS9A1A3R24A2R23A3S3S28S26R25R24S82R25A1A3S29A3S3S28S11aS82R26A1S6aA2S29A3S3S28S130S6aSeS23R27A1A1A2S29A3S3S28S4fSeS23R28A1A1S73S30R2dA1R2cA2A2S29A3S3S28S11fS82R29A1S77S77A3S29A3S3S28S15bSaS23R2aA1A1S60S82R2aA1S54S73S30R2fA1R2eA2A1M11A2G11A3S29A3S3S28S50S49S82R2bA1G9A2G9A2S29A3S3G2S102S127S78R2dR28R27S133S7fR30A1A6Sb2R2fS30R31A1A2A2S2fS22R2aA2A3S4S3GfS11dS113R2eR29S133A3M12S132A2G6A3S3S4aS49G12S47S138S31A2A2S47S7eS31A2A3A2S3G2S102S127S78R2fR2aR29S134S7fR32A1A6Sb2R31S30R33A1A2A2S2fS22R2bA2A3S4S3GfS11dS113R30R2bS134A3M13S132A2G6A3S3S4aS49G13S47S137S29A2A2S47SacS29A2A3A2S67S2aG3S2aS0S7A2M14A2M15S2bG3G14S2bS22S45R2fS73S30R35A1R34A2A4S2bS0S7R2aS7aA4A4S79A3S67G15S2bG3G14S2bS22S45R2fSa6S30R36A1S7eA2A4S2bS0S7R2bS7aA4A4S79A3S67G15S2bG3G14S2bS22S45R2fSa7S30R37A1SacA2A4S2bS0S7R2cS7aA4A4S79A3S3fGaR2dA2S3fS40S41R2eZ1A2S42Z2G5A2A2R2bA2VTR;S3aS39VJAv;S48S77G7S2cS5eS74R3aS75A2G8A3G9A4A1R37R2eR2dA5VFAM;R2cR2bA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FrkT;FR;Fs;FTok;FTf;FTzG;FTz;FE;FE0;Fpidx;Fv;Fj;").
Proof.
  intros j v pidx E0 E Tz TzG Tf Tok s R rkT rho tp b tp0 Hj HE Hck HkB Hb47 HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham Hpay Hpd HR HX Hs12 Hs15 Hs17 Hoff
         HTz Himp_z HTzG Hze Hzid Hznp Hznb Hztv Hzbd Hzam HTf Himp_f HTok Himp_ok HinZ HinF HinOk Hrk Hb.
  assert (Hv : In v fins) by (eapply nth_error_In; exact Hj).

  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true))) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ _ rho _ E tp w HE Hw) as Hw2.
    apply (JA_repay segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k)
             (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true) E rho tp w); [|exact Hw2].
    exact (pay_fin j v (ss_facts (ax_S E)) (bd_push sh_c sh_k) Hj eq_refl Hck HkB). }

  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  change (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) with (CHf v (vd_c v) ++ CHfrom (S j) cs0 ++ bd_push sh_c sh_k).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX (VFP.P0_vf CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vf VFZ.nd0z PD_vf NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVF eq_refl
           E s R (Xk_vf v) rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom (S j) cs0 ++ bd_push sh_c sh_k) (AHead vHq true) (FAM b tp0)
           HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). exact Hpay.
  - exact Hpd.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E R (Xk_vf v) keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR Hb47 HR HX) as [A B].
    split; [exact A|]. split; [exact B|].
    destruct (P0_now rho Hav HP0) as [PB PA].
    pose proof (holds_mem _ _ _ HF Hb47) as F47. zf F47. unfold two47, RA.two47 in F47. rewrite uval_lit in F47 by lia.
    unfold VFP.P0_vf. unfold uval, VF.vV, VF.vD, VF.vL. cbn [eval]. rewrite !rw_call', Hs12, Hs15, Hs17.
    change (bv_unsigned (eval rho (bofs (vd_off v)))) with (uval rho (bofs (vd_off v))). rewrite (bofs_val rho (vd_off v)) by (unfold two47, RA.two47; lia).
    split.
    + intros a Ha. eapply (infrFF_pclMA CST _ FF); [exact PB | lia].
    + change (bv_unsigned (eval rho (vd_d v))) with (uval rho (fst (Xof v))). change (bv_unsigned (eval rho (kb (vd_el v) (vd_k v)))) with (uval rho (snd (Xof v))).
      assert (HinK : In (Xof v) keptF) by (apply in_or_app; left; apply in_map; exact Hv).
      destruct (Z.eq_dec (uval rho (fst (Xof v))) 0) as [Hz|Hnz].
      * left. pose proof (proj1 (Forall_forall _ _) HZ1 (Xof v) HinK) as X. cbv beta in X. unfold tnz, tvv in X. cbn [snd] in X.
        unfold uval in *. apply X. intros Y. exact (Y Hz).
      * right; left. exists (fst (tvv rho (Xof v))), (snd (tvv rho (Xof v))). split; [|unfold tvv; cbn [fst snd]; unfold uval; lia].
        apply In_FBx. right. exists (Xof v). split; [exact HinK|]. split; [exact Hnz | symmetry; apply surjective_pairing].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vf In] in Hd.
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am VFZ.nd0z VF.nd_fail VF.nd_ok VF.nd0];
      fold (isub_vf E s VF.P_zero); fold (isub_vf E s VF.P_fail); fold (isub_vf E s VF.P_ok).
    +
      destruct Himp_z as (Hi1 & Hi2 & Hi3). rewrite Hi1, Hi2, Hi3.
      eapply TR_pre; [|apply (REENTER TzG (ndTz (S j) v) (rkT, z0) (rho_sub rho' (s_gh Tz))); [exact HinZ | rewrite emeas_z0; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ _ rho' _ Tz tp' w HTz Hw) as Hw1. subst TzG.
      apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc Tz (ax_add_facts [ghZ] Tz) (s_gh Tz) (ndTz (S j) v) (ndTz (S j) v));
        [exact Hze | exact Hzid | exact Hznp | exact Hznb | exact Hztv | reflexivity | exact Hzbd | exact Hzam |].
      unfold ndTz, tv0. exact Hw1.
    +   rewrite (proj1 Himp_f), (proj2 Himp_f). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tf (ndTf (S j) vHq) (rkT, z0) rho'); [exact HinF | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' _ Tf tp' w HTf Hw).
    +   rewrite (proj1 Himp_ok), (proj2 Himp_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tok (ndTok (S j) vHv) (rkT, z0) rho'); [exact HinOk | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' _ Tok tp' w HTok Hw).
Qed.
Lemma X_E_vf5 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z6aS42Z2Z40A2A2R2A2VTR;S3aS39VJAv;Sd5A1Sb9R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd5.
  apply (X_VF 4 vLI 12 E_vf5_0 E_vf5 T5_z T5_zG T5_f T5_ok s_vf5 R_vf5 105 rho tp b tp0 eq_refl E_vf5_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| cbn; lia
    | exact T5_z_eq | exact imp_vf5_z | exact T5_zG_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T5_f_eq | exact imp_vf5_f | exact T5_ok_eq | exact imp_vf5_ok | innth 15 | innth 17 | innth 16 | lia | lia].
Qed.
Lemma X_E_vf6 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z60S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;Sd6A1SbaR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd6.
  apply (X_VF 5 vLC 13 E_vf6_0 E_vf6 T6_z T6_zG T6_f T6_ok s_vf6 R_vf6 95 rho tp b tp0 eq_refl E_vf6_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| cbn; lia
    | exact T6_z_eq | exact imp_vf6_z | exact T6_zG_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T6_f_eq | exact imp_vf6_f | exact T6_ok_eq | exact imp_vf6_ok | innth 19 | innth 21 | innth 20 | lia | lia].
Qed.
Lemma X_E_vf7 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z56S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;Sd7A1SbbR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd7.
  apply (X_VF 6 vPI 14 E_vf7_0 E_vf7 T7_z T7_zG T7_f T7_ok s_vf7 R_vf7 85 rho tp b tp0 eq_refl E_vf7_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| cbn; lia
    | exact T7_z_eq | exact imp_vf7_z | exact T7_zG_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T7_f_eq | exact imp_vf7_f | exact T7_ok_eq | exact imp_vf7_ok | innth 23 | innth 25 | innth 24 | lia | lia].
Qed.

Lemma kb_val : ltac2:(tb__ "0|0|
S8S0S7S4S3fZ1R2A2S3fR2Z80A2A2S3fS5dR4R2A2S72A2S3S0S5dR5S6fR4R3A2A2S40R4S5dR5R3A2A2A3F_;F_;Fk;Fe;Frho;").
Proof. intros rho e k He Hk. unfold kb, B32, Lib_vec_reserve.B32 in *. pose proof (uval_range rho k). apply uval_mul_lit; nia. Qed.

Lemma X_E_vp : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z4cS42Z2Z40A2A2R2A2VTR;S3aS39VJAv;Sd8A1SbcR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd8, tv0.
  eapply TR_pre with (P := SPA segs (JAv (NDA (keptP ++ [Xof vSH]) [] (bd_push sh_c sh_k) (AHead vHq true))) E_vp rho tp).
  { intros w Hw. apply (SPA_axforms segs _ _ rho _ E_vp tp w E_vp_eq).
    unfold keptP. rewrite <- app_assoc. cbn [app]. apply (SPA_tv_swap (map Xof fins) (Xof vSH) (vAR, SLit 64)). exact Hw. }
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX VPP.P0_vp PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vp (ndh hVP true VP.ndp0) (PDh PD_vp hVP true) NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVP eq_refl
           E_vp s_vpH R_vp Xk_vp rho tp keptP [Xof vSH] [] _ [] (AHead vHq true) (FAM b tp0)).
  - vmr.
  - exact R_vp_eqH.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). vmr.
  - vmr.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptP _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E_vp R_vp Xk_vp keptP rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR ltac:(vmr) ltac:(vmr) ltac:(vmr)) as [A B].
    split; [exact A|]. split; [exact B|].
    destruct (P0_now rho Hav HP0) as [PB PA].
    factz HF (SPUle vB (SLit two47)) F47. unfold two47, RA.two47 in F47. rewrite uval_lit in F47 by lia.
    factz HF (SPUle sh_k (SLit B32)) FK. unfold B32, Lib_vec_reserve.B32 in FK. rewrite uval_lit in FK by lia.
    unfold VPP.P0_vp. rewrite !rw_call'. change (wsub_get s_vpH 17) with sh_k. change (wsub_get s_vpH 15) with sh_d.
    change (wsub_get s_vpH 12) with (bofs 448). change (wsub_get s_vpH 13) with vAL.
    change (bv_unsigned (eval rho (bofs 448))) with (uval rho (bofs 448)). rewrite (bofs_val rho 448) by (unfold two47, RA.two47; lia).
    split; [|split].
    + intros HK HD0. pose proof (proj1 (Forall_forall _ _) HZ (Xof vSH) ltac:(apply in_or_app; right; left; reflexivity)) as X. cbv beta in X.
      unfold tnz, tvv in X. cbn [fst snd Xof vSH vd_d vd_k vd_el] in X. specialize (X ltac:(intros Y; exact (Y HD0))).
      change (bv_unsigned (eval rho (kb 128 sh_k))) with (uval rho (kb 128 sh_k)) in X. rewrite kb_val in X by (unfold B32, Lib_vec_reserve.B32; lia).
      unfold uval in X. lia.
    + destruct PB as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | lia].
    + destruct PA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | unfold uval in H1, H2; lia].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PDh PD_vp map In] in Hd.
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am ndh VP.ndp0 VP.ndpG ND]; fold (isub_vp VP.P_push_keep); fold (isub_vp VP.P_push_fail); fold (isub_vp VP.P_push_grown).
    +   destruct imp_vp_keep as (Hi1 & Hi2 & Hi3). cbn [nd_tv nd_bd VP.ndp0 ND] in Hi1, Hi2. rewrite T_pk0_eqH, Hi1, Hi2, Hi3, app_nil_r.
      eapply TR_pre; [|apply (REENTER T_pkF ndPk (75, z0) rho'); [innth 27 | rewrite emeas_z0; lia]].
      intros w Hw. unfold keptP in Hw. rewrite <- app_assoc in Hw. cbn [app] in Hw. apply (SPA_tv_swap (map Xof fins) (vAR, SLit 64) (Xof vSH)) in Hw.
      pose proof (SPA_axforms segs _ _ rho' _ T_pk tp' w T_pk_eq Hw) as Hw1.
      rewrite <- T_pkF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | vmr |].
      intros tr md HJ HF2.
      assert (TNZ : tnz rho' (Xof vSH)).
      { factz HF2 (SPUle (SAlu ALU_ADD sh_c (SLit 1)) sh_k) F1. factz HF2 (SPUle sh_k (SLit B32)) F2. unfold B32, Lib_vec_reserve.B32 in F2. rewrite uval_lit in F2 by lia.
        factz HF2 (SPUle sh_c sh_k) F0.
        pose proof (uval_range rho' sh_c). rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
        intros Hz. pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue _ rho' tp' tr md (Xof vSH) HJ ltac:(apply in_or_app; right; left; reflexivity) Hz) as Z0.
        cbn [snd Xof vSH vd_el vd_k] in Z0. change (bv_unsigned (eval rho' (kb 128 sh_k))) with (uval rho' (kb 128 sh_k)) in Z0. rewrite kb_val in Z0 by (unfold B32, Lib_vec_reserve.B32; lia). lia. }
      pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ALA _ _ _ _ _ (Xof vSH) eq_refl HJ ltac:(apply in_or_app; right; left; reflexivity) TNZ) as TF.
      constructor; [|constructor; [|exact HF2]].
      * apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, hse_fact. cbn [fst snd Xof vSH vd_d]. do 5 right. left. reflexivity.
      *
        apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, top_factK. cbn [fst snd Xof vSH vd_d vd_k vd_el]. do 2 right. left. reflexivity.
    +   destruct imp_vp_fail as [Hi1 Hi2]. rewrite T_pf0_eqH, Hi1, Hi2. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER T_pf ndPf (75, z0) rho'); [innth 28 | rewrite emeas_z0; lia]].
      intros w Hw. unfold keptP in Hw. rewrite <- app_assoc in Hw. cbn [app] in Hw. apply (SPA_tv_swap (map Xof fins) (vAR, SLit 64) (Xof vSH)) in Hw.
      exact (SPA_axforms segs _ _ rho' _ T_pf tp' w T_pf_eq Hw).
    +   destruct imp_vp_grown as (Hi1 & Hi2 & Hi3). cbn [nd_tv nd_bd VP.ndpG ND] in Hi1, Hi2. rewrite T_pg0_eqH, Hi1, Hi2, Hi3, app_nil_r.
      eapply TR_pre; [|apply (REENTER T_pgF ndPg (75, z0) rho'); [innth 29 | rewrite emeas_z0; lia]].
      intros w Hw. unfold keptP in Hw. rewrite <- app_assoc in Hw. cbn [app] in Hw. apply (SPA_tv_swap (map Xof fins) (vAR, SLit 64) (vDg, kb 128 vKg)) in Hw.
      pose proof (SPA_axforms segs _ _ rho' _ T_pg tp' w T_pg_eq Hw) as Hw1.

      rewrite <- T_pgF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | vmr |].
      intros tr md HJ HF2. constructor; [|exact HF2].
      assert (TNZ : tnz rho' (vDg, kb 128 vKg)).
      { factz HF2 (SPNot (SPBranch BC_EQ vDg (SLit 0))) F0. rewrite uval_lit in F0 by lia. unfold tnz. cbn [fst]. unfold uval in F0. exact F0. }
      pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ALA _ _ _ _ _ (vDg, kb 128 vKg) eq_refl HJ ltac:(apply in_or_app; right; left; reflexivity) TNZ) as TF.
      apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, top_factG. cbn [fst snd]. do 2 right. left. reflexivity.
Qed.

Lemma slot_rng : ltac2:(tb__ "0|d|
S8S27S9A1S7S7Sf5S9S11R4A1R3A3S3S28S66S9SbScR3S14P1eA1M0A2A1R4A3S29A3S3S28S66S9SbScS10Sf7R4S6fZ80M1R3A2A3G0A2A1R5A3S29A3S3S28S66S9SbScS10Sf7S71SdZ1A1A3R4A2A1R6A3S29A3S3S28S66S9SbScR5SdS72A1M2A2A1R7A3S29A3S3S28S66S9SbScS71S7dA2A1R8A3S29A3S3S28S66S9SbScS7dG2A2A1R9A3S29A3S3S28S66S9SbScG0SdZ7fffff800000M3A1A2A1RaA3S29A3S4S3S0S5dRcS6fG1S71A2M4A2S40G1S5dRcS71A2A2M5A3S4S3S0S16RcS10Sf7G4SdZ38M6A1M7A3A2S41G5G6A2A3S4S3S0S16RcS10Sf7G4SdZ48M8A1A3A2S41G5G8A2A3S4S3S0S5dRcSaaRaA1M9A2S41S5dRcRaA2MaG5A2MbA3S4S3S0S5dRcS10Sf7G9G7A3A2S41GbG6A2A3S4S3fS41G5G1A2S40G1S5dRcR9A2A2McA2S4S3S0S5dRcS6fG1R9A2A2GcA3S3fS41GaGcA2G3A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fk;Fd;FF;Fr;").
Proof.
  intros r F d k HF H1 H2 H3 H4 H5 H6 H7.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H4) as F4. pose proof (holds_mem _ _ _ HF H5) as F5. pose proof (holds_mem _ _ _ HF H6) as F6.
  pose proof (holds_mem _ _ _ HF H7) as F7.
  zf F1. zf F2. zf F3. zf F4. zf F5. zf F6. zf F7. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in *.
  unfold B32, Lib_vec_reserve.B32 in *. rewrite uval_lit in F4 by lia. rewrite uval_lit in F6 by lia. rewrite uval_lit in F7 by lia.
  pose proof (uval_range r sh_c) as RC. pose proof (uval_range r d) as Rd. pose proof (uval_range r k) as Rk.
  rewrite uval_add_small in F3 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F3 by lia.
  assert (EK : uval r (kb 128 k) = 128 * uval r k) by (apply kb_val; unfold B32, Lib_vec_reserve.B32; lia).
  assert (EC : uval r (kb 128 sh_c) = 128 * uval r sh_c) by (apply kb_val; unfold B32, Lib_vec_reserve.B32; lia).
  rewrite uval_add_small in F2 by (rewrite EK; lia). rewrite EK in F2.
  assert (A56 : uval r (SAlu ALU_ADD (kb 128 sh_c) (SLit 56)) = 128 * uval r sh_c + 56) by (rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia); rewrite EC, uval_lit by lia; lia).
  assert (A72 : uval r (SAlu ALU_ADD (kb 128 sh_c) (SLit 72)) = 128 * uval r sh_c + 72) by (rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia); rewrite EC, uval_lit by lia; lia).
  assert (AS : uval r (slotx d) = uval r d + 128 * uval r sh_c) by (unfold slotx; rewrite uval_add_small by (rewrite EC; lia); rewrite EC; lia).
  split; [exact EC|]. split; [rewrite soff_smallu by (rewrite A56; lia); exact A56|]. split; [rewrite soff_smallu by (rewrite A72; lia); exact A72|].
  split; [exact AS|]. split; [rewrite uval_add_small by (rewrite AS, uval_lit by lia; lia); rewrite AS, uval_lit by lia; lia|]. lia.
Qed.
Definition slotF (F : list sprop) (d k : sv) : bool := ltac2:(tb__ "0|2|
S32S32S32S32S32S32S66S9SbScVd;S14P1eA1M0A2A1VF;A3S66S9SbScS10Sf7Vd;S6fZ80Vk;A2A3G0A2A1VF;A3A2S66S9SbScS10Sf7S71SdZ1A1A3Vk;A2A1VF;A3A2S66S9SbScVk;SdS72A1M1A2A1VF;A3A2S66S9SbScS71S7dA2A1VF;A3A2S66S9SbScS7dG1A2A1VF;A3A2S66S9SbScG0SdZ7fffff800000A1A2A1VF;A3A2").
Lemma slot_rngF : ltac2:(tb__ "0|a|
S8S27S9A1S7S7Sf5S9S11R4A1R3A3S3S28S148R4R3R2A3S29A3S4S3S0S5dR6S6fZ80M0S71A2M1A2S40G0S5dR6S71A2A2M2A3S4S3S0S16R6S10Sf7G1SdZ38M3A1M4A3A2S41G2G3A2A3S4S3S0S16R6S10Sf7G1SdZ48M5A1A3A2S41G2G5A2A3S4S3S0S5dR6SaaR4A1M6A2S41S5dR6R4A2M7G2A2M8A3S4S3S0S5dR6S10Sf7G6G4A3A2S41G8G3A2A3S4S3fS41G2G0A2S40G0S5dR6R3A2A2M9A2S4S3S0S5dR6S6fG0R3A2A2G9A3S3fS41G7G9A2Z7fffff800000A2A2A2A2A2A2A2A2F_;F_;Fk;Fd;FF;Fr;").
Proof.
  intros r F d k HF H. unfold slotF in H. repeat (apply andb_prop in H as [H ?]).
  eapply slot_rng; eassumption.
Qed.

Lemma X_MS : ltac2:(tb__ "0|c|
S22S22S22S22S22S27SfA1M0S7S7S45S8S27S3dQ40A1A1M1S0G1S3S33S22A1M2S102RdSe2A2S2fS22RcA2A3S3S22S25RdS15aS23RdA1U1dM3Sa1R8A1A3A2RcA3S3S33SfA1M4S68SfS12S23ReA1A1G3A3S2fSfS91R9A1A2A3S3S28S1cSeS23RfA1A1Sa1RaA1A2S29A3S3S28S148SaS23R10A1A1RbRaA3S29A3S3S33G0A1Se7R10S86S8bR10RcRbA3A3S2fG0RdA2A3S3S28Se6R11S86S8bR11RdRcA3ReS2dS22S8cS2eS22A1A3A5S29A3S3S28S14bS6aS8bR12ReRdA3A2S29A3S3S28S130S6aSeS23R13A1A1A2S29A3S3S28S4fSeS23R14A1A1ReA2S29A3S3S28S62SeS23R15A1A1S54RfA1A2S29A3S3S28S63S54R10A1A1S29A3S3S27S2aS2aS7S0A2S7A2M5A1S55R11A1S2eG5A1M6A3S3S28S66S9SbScS6bSdS70A1A2A1SaS23R18A1A1A3S29A3S3S28S12fSaS23R19A1A1S4bR13A1G6S36S35A1M7SeaR16A6S29A3S3S28S123VXGL;SaS23R1aA1M8A1S4bR14A1G6G7S12G8A1SebS24R1aA1A8S29A3S3S22S14dS86R1bS8bR1bR17R16A3R18S8cA5R1aA3S3G4S68SfS12S23R1bA1A1U1M9A3S2fSfS115R18A1A2A3S3S28S1cSeS23R1cA1A1S91R19A1A2S29A3S3S28S148SaS23R1dA1A1R1aR19A3S29A3S3G2S102S25R1eS15aS23R1eA1G9S91R1bA1A3A2Se1A2S2fS22R1dA2A3S67S2aS2aS22S45A2MaS2aS0S7A2MbA2S2bGaGbS2bS22S45R1eR1aA4S2bS0S7Z41S7aA4A4S79A3S3fS40Z42S42Z2Z40A2A2R18A2VTR;S3aS39VJAv;R1cA1R24R1bR1aA5VFAM;R19R18A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fnd;Fk;Fd;FR;FTm;FTm0;FE;FE1;FE0;").
Proof.
  intros E0 E1 E Tm0 Tm R d k nd rho tp b tp0 HE1 HE Hn29 Hwf HSF He Hchk Hta Hnp Hnb Hbb Hwp Hfr H47 HR HX HTm0 Hn1 Hwf2 HSF2 HTm HinM Hb.
  eapply TR_pre with (P := SPA segs (JAv nd) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_mcall rho E0 E1 tp w HE1 Hw) as Hw1. rewrite <- HE.
    apply (SPA_reshape segs _ rho E1 29 _ _ tp w Hn29); [reflexivity | reflexivity | reflexivity | exact Hwf | | exact Hw1].
    intros HF. destruct (slot_rngF rho _ d k HF HSF) as (EC & A56 & A72 & AS & AS56 & Hck & EK & Hd).
    unfold hole_obj, mid_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A56, A72.
    change (bv_unsigned (eval rho (SAlu ALU_ADD (slotx d) (SLit 56)))) with (uval rho (SAlu ALU_ADD (slotx d) (SLit 56))). rewrite AS56. unfold uval. lia. }
  destruct nd as [tvN frN bdN amN]. cbn [nd_tv nd_fr nd_bd nd_am] in *. subst frN.
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E (s_m E d k) R rho tp (NDA tvN [] bdN amN) bdN (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMSET Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact He.
  - exact Hchk.
  - exact Hta.
  - exact Hnp.
  - exact Hnb.
  - exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - vmr.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
    destruct (site_rt E R tvN rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HBf HFF HN HD HZ HFR H47 HR HX) as [A B].
    split; [exact A|]. split; [exact B | exact I].
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E memset_pc (s_m E d k) R rho tp tr ms md Hsm HM HX' He).
  - intros L rho' tp' [<-|[]] Hag. cbn [nd_tv nd_fr nd_am]. rewrite HTm0.
    eapply TR_pre; [|apply (REENTER Tm (NDA tvN [] bdN amN) (65, z0) rho'); [exact HinM | rewrite emeas_z0; lia]].
    intros w Hw.
    assert (Hw1 : SPA segs (JAv (NDA tvN [] bdN amN)) (ax_setS Tm0 (reshape_obj_at (ax_S Tm0) 1 (mid_obj d))) rho' tp' w).
    { apply (SPA_reshape segs _ rho' Tm0 1 _ _ tp' w Hn1); [reflexivity | reflexivity | reflexivity | exact Hwf2 | | exact Hw].
      intros HF. destruct (slot_rngF rho' _ d k HF HSF2) as (EC & A56 & A72 & AS & AS56 & Hck & EK & Hd).
      unfold holeZ, mid_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A56, A72.
      change (bv_unsigned (eval rho' (SAlu ALU_ADD (slotx d) (SLit 56)))) with (uval rho' (SAlu ALU_ADD (slotx d) (SLit 56))). rewrite AS56. unfold uval. lia. }
    exact (SPA_axforms segs _ xf_mback rho' _ Tm tp' w HTm Hw1).
Qed.
Lemma X_E_mk : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z42S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;SdbA1Sb8R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_MS E_mk0 E_mk1 E_mk T_mk0 T_mk R_mk sh_d sh_k ndPk rho tp b tp0 E_mk1_eq E_mk_eq nth29_mk1);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|reflexivity|reflexivity|vmr|vmr|vmr| exact T_mk0_eq | exact nth1_Tmk0 |vmr|vmr| exact T_mk_eq | innth 30 | exact Hb].
Qed.
Lemma X_E_mg : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z42S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;SdaA1Sb7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_MS E_mg0 E_mg1 E_mg T_mg0 T_mg R_mg vDg vKg ndPg rho tp b tp0 E_mg1_eq E_mg_eq nth29_mg1);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|reflexivity|reflexivity|vmr|vmr|vmr| exact T_mg0_eq | exact nth1_Tmg0 |vmr|vmr| exact T_mg_eq | innth 31 | exact Hb].
Qed.

Lemma X_FL : ltac2:(tb__ "0|6|
S22S22S27S5eA1S7S8S27S3dQ40A1A1M0S0G0S67S2aS22Se4A2S2bS22Se4R7SfbS8aA1A4SfcA3S3S28S26R9R8S125S6aS23R9A1M1S23R8A1A3A3S29A3S3S28S11aS125S6aS23RaA1G1A3S6aA2S29A3S3S28S130S6aSeS23RbA1A1A2S29A3S3S28S4fSeS23RcA1M2A1S48S77S2eS2aS2aS7S0A2S7A2A1M3RaS47R9S31A2A4A2S29A3S3S28S11fS125S6aS23RdA1M4G2A3S77S77A3S29A3S3S28S15bSaS23ReA1M5A1S60S125S6aG5G4A3S2eS5eA1A2RcA3S29A3S3S28S50S49S125S6aS23RfA1G5A3S47SddS31A2A2S47RcS31A2A2S29A3VTR;S3aS39VJAv;S48S77G3ReS47RdS29A2A4A1R10RcRbA5VFAM;RaR9A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fhq;Fbd;FP;FFL;").
Proof.
  intros FL P bd hq rho tp b tp0 HinP He Hid Hnp Hnb Htv Hbd Ham.
  eapply TR_pre; [|apply (POST P nd_fail_f (rho_sub rho (infer_sub NP (ax_S FL) (ax_S P))) tp b tp0 HinP)].
  intros w Hw. unfold nd_fail_f.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc FL P _ (NDA tv0 [] bd (AHead hq false)) (NDA tv0 [] [] (AHead qHD false)));
    [exact He | exact Hid | exact Hnp | exact Hnb | exact Htv | reflexivity | exact Hbd | exact Ham |].
  apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HBX). exact Hw.
Qed.
Tactic Notation "xfl" constr(P) integer(k) := intros; apply (X_FL _ P); [do k right; left; reflexivity |vmr|vmr|vmr|vmr|vmr|vmr|vmr].
Lemma X_FL_E0 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S76A1Sc3R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndE, nd0. xfl P_failz 3. Qed.
Lemma X_FL_E1 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S76A1Sc4R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndE, nd0. xfl P_fail 2. Qed.
Lemma X_FL_50 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S73U5SaeA2A1SbdR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_fail 2. Qed.
Lemma X_FL_51 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S73U5SaeA2A1SbeR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_failz 3. Qed.
Lemma X_FL_60 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S73U6SadA2A1SbfR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_fail 2. Qed.
Lemma X_FL_61 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S73U6SadA2A1Sc0R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_failz 3. Qed.
Lemma X_FL_70 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S73U7SafA2A1Sc1R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_fail 2. Qed.
Lemma X_FL_71 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;S73U7SafA2A1Sc2R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_failz 3. Qed.
Lemma X_FL_p0 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;Sa4A1Sc5R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndPf. xfl P_fail 2. Qed.
Lemma X_FL_p1 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0VTR;S3aS39VJAv;Sa4A1Sc6R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndPf. xfl P_failz 3. Qed.

Lemma X_X_N0 : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0S0G0S3fS40Z97S42Z2Z40A2A2R2A2VTR;S3aS39VJAv;S76A1S87R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply NAMEBLK.
  - intros rho' tp'. apply (REENTER C_1 nd1 (150, z0)); [innth 2 | rewrite emeas_z0; lia].
  - intros P nd rho' tp' HinP. apply POST. exact HinP.
Qed.

Lemma J_parts : ltac2:(tb__ "0|1|
S45S8S27S3dQ40A1A1S27Sf4A1Sf3VJAv;R5R4R3R2R1A5S5Sf0Sf0S4VAInv;R1R6R5R3A4S4S104S6aVrho0;R6A3S4Se9VFB;VFF;Vrho0;A3S4S56VFB;R1A2S4S52VFF;R1A2S4S4dVFB;R1R6S4bR7A1M0A4S4S11eR6G0A2S4S11cR6G0A2S4S53VFF;R1R6S55R7A1A4S4S51Vrho0;R1A2S120R6Sf2Sf1R1A1A1A2A2A2A2A2A2A2A2A2A2A2LAi;A2F_;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md (Ai & kc & Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & _). exists Ai. repeat (split; [assumption|]).
  exact (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT).
Qed.

Lemma site_arena : ltac2:(tb__ "0|4|
S22S27SfA1S27S2aS7S7A2A1S45S8S27S3dQ40A1A1S27Sf4A1Sf3VJAv;R5R4R3R2R1A5S3S27S2aS2aS7S0A2S7A2M0A1S55R6A1S2eG0A1M1A3Sf5S9S11R6A1SaS23RaA1A1A3S3S28S66S9SbScS6bSdS70A1A2A1SaS23RbA1A1A3S29A3S3S28S124SaS23RcA1A1S4bR9A1G1S36S35A1M2SeaRbA6S29A3S3S28S123VXGL;SaS23RdA1M3A1S4bRaA1G1G2S12G3A1SebRbA8S29A3S4S154VCST;Vrho0;VFB;VFF;RaS4bRbA1G1RdA8S152RaRcA2A2F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fnd;FX;Fobjs;FA;").
Proof.
  intros A objs X nd rho tp tr md HJ Hfr HF H47 HR HX.
  destruct (J_parts nd rho tp tr md HJ) as (Ai & HM & Hav & HP0 & HBf & HFF & HN & HD & HZ & HFR & HT & HTK). rewrite Hfr in HFR.
  pose proof (b47_of rho _ HF H47) as Hb. split.
  - exact (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho _ (nd_tv nd) [] fr_obj objs rho tp md HM HF HT HTK HN HD HZ HFR HR
             (fun o' a' Ho' HE Hr' => fr_obj_pclMA rho o' a' _ Hav HP0 HE Hr')).
  - exact (proj2 (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho _ (nd_tv nd) [] None (ss_objs (ax_S A)) fr_xr X rho tp md HM HF HT HTK HBf HFF HN HD HZ HFR HX
             (fun r' a' Hr' HE Ha' => or_introl (fr_xr_pclMA rho r' a' _ Hav HP0 Hb HE Ha')))).
Qed.
Lemma xrs47_cons : ltac2:(tb__ "0|1|
S8S7S7S27S2aS7S7A2M0A1S3fS41S5dR4R3A2S41S5dR4R2A2Z20A2A2Z7fffff800000A2S152R5R2A2S152R6S2dG0S2bS7S7R5S153R4A1A4R3A3A2F_;F_;FX;Fc;Fh;Frho;").
Proof.
  intros rho h c X Hh HX r a [<-|Hr] Ha; [|exact (HX r a Hr Ha)]. cbn [fst snd] in Ha.
  pose proof (uval_range rho c). pose proof (uval_range rho h). unfold e32 in Ha.
  rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia. lia.
Qed.
Ltac measN := rewrite emeas_z0; lia.
Tactic Notation "innthN" integer(n) := cbn [In cutsN]; do n right; left; reflexivity.

Lemma XN_open0 : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0S3fS40Z5bS42Z2Z40A2A2R1A2VTR;S3aS39VJAv;S76A1ScbR4R3A5VFAMN;R2A1A2F_;Fb;Ftp;Frho;").
Proof.
  intros rho tp b Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros [tr [ms md]] Hw0. pose proof (proj2 Hw0) as HJ. cbn [w_tr w_cfg cfg_model] in HJ.
    pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw0)) as HF.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd0 vHD true X_open0 rho tp (tr, mkCfg ms md))
      as (rho' & _ & Hw'); [vmr | reflexivity | vmr | vmr | vmr | | exact Hw0 |].
    - intros Ai rho1 tp1 md1 _ _ _ _ _ _. exact (site_arena X_open0 (ss_objs (ax_S X_open0)) (ax_X X_open0) ndE rho tp tr md HJ eq_refl HF ltac:(vmr) ltac:(vmr) ltac:(vmr)).
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER_N C_open ndO (90, z0)); [innthN 1 | measN].
Qed.

Lemma XN_nohead : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0S3fS40Z51S42Z2Z40A2A2R1A2VTR;S3aS39VJAv;S76A1Sc9R4R3A5VFAMN;R2A1A2F_;Fb;Ftp;Frho;").
Proof.
  intros rho tp b Hb.
  eapply TR_pre; [|apply (REENTER_N C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innthN 2 | measN]].
  intros w Hw0. unfold ndS.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (bd0 ++ [BIc 1 0 AV0; BIc 0 1 AK0]) am_np) (NDA tv0 [] (bd0 ++ POT vUg) am_np));
    [vmr | vmr | vmr | vmr | vmr | reflexivity | vmr | vmr |].
  apply (JA_pot_out0 segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HBX); [vmr | exact Hw0].
Qed.

Lemma XN_nofit : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0S3fS40Z51S42Z2Z40A2A2R1A2VTR;S3aS39VJAv;Sa3A1Sc8R4R3A5VFAMN;R2A1A2F_;Fb;Ftp;Frho;").
Proof.
  intros rho tp b Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) ohNF rho tp tr ms md objsNF_eq ltac:(vmr) ltac:(vmr) ltac:(vm_compute; left; reflexivity) eq_refl Hw) as CL.
    rewrite X_nofit1_eq in CL. set (rho1 := rho_absorb rho [ohNF] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vmr |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      factz HF (SPNot (SPBranch BC_GEU vCAP (SAlu ALU_ADD vU (SLit 1)))) H0. factz HF (SPUle (SLit 65536) vCAP) H1. factz HF (SPUle vCAP (SLit (2 ^ 40 - 33))) H2.
      rewrite uval_lit in H1 by lia. rewrite uval_lit in H2 by lia. pose proof (uval_range rho vU).
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65536 mod M64v) with 65536. rewrite EU. change (bv_unsigned (eval rho vU)) with (uval rho vU).
      destruct (Z_lt_dec (uval rho vU + 1) (2 ^ 64)); [rewrite uval_add_small in H0 by (rewrite uval_lit by lia; lia); rewrite uval_lit in H0 by lia; lia | lia]. }
    exists (rho_sub rho1 s_nofit). unfold ndS.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) (NDA tv0 [] (bd0 ++ POT vUg) am_np));
      [vmr | vmr | vmr | vmr | vmr | reflexivity | vmr | vmr | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER_N C_slow ndS (80, z0)); [innthN 2 | measN].
Qed.

Lemma XN_fit : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0S3fS40Z33S42Z2Z40A2A2R1A2VTR;S3aS39VJAv;Sa3A1Sc7R4R3A5VFAMN;R2A1A2F_;Fb;Ftp;Frho;").
Proof.
  intros rho tp b Hb. apply TR_facts. intros HF.
  factz HF (SPBranch BC_GEU vCAP (SAlu ALU_ADD vU (SLit 1))) H0. factz HF (SPUle (SLit 65536) vCAP) H1. factz HF (SPUle vCAP (SLit (2 ^ 40 - 33))) H2.
  factz HF (SPUle vHD (SVar 30)) H3. factz HF (SPUle (SAlu ALU_ADD vHD (e32 vCAP)) (SVar 30)) H4. factz HF (SPUle vU vCAP) H5.
  factz HF (SPUle (SLit 4096) vHD) H6. rewrite uval_lit in H6 by lia.
  rewrite uval_lit in H1 by lia. rewrite uval_lit in H2 by lia. factz HF (SPUle (SVar 30) (SLit 140737479966720)) HT30. rewrite uval_lit in HT30 by lia.
  pose proof (uval_range rho vU) as RU. pose proof (uval_range rho vHD) as RH.
  assert (EK : uval rho (e32 vCAP) = uval rho vCAP + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite uval_add_small in H4 by (rewrite EK; lia). rewrite EK in H4.
  rewrite uval_add_small in H0 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H0 by lia.
  assert (EP : forall r, uval r vHD <= 140737479966720 -> uval r vU <= uval r vCAP -> uval r vCAP <= 2 ^ 40 - 33 ->
            uval r pfit0 = uval r vHD + uval r vU + 32 /\ uval r (SAlu ALU_ADD pfit0 (SLit 1)) = uval r pfit0 + 1 /\ uval r (SAlu ALU_ADD vHD (SLit 32)) = uval r vHD + 32
            /\ uval r (SAlu ALU_ADD vHD (e32 vCAP)) = uval r vHD + (uval r vCAP + 32)).
  { intros r Rh Ru Rc. pose proof (uval_range r vU). pose proof (uval_range r vHD). pose proof (uval_range r vCAP).
    assert (E1 : uval r pfit0 = uval r vHD + uval r vU + 32).
    { unfold pfit0. rewrite uval_add_small by (rewrite uval_add_small by lia; rewrite uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
    assert (E2 : uval r (e32 vCAP) = uval r vCAP + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    split; [exact E1|]. split; [rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia); rewrite uval_lit by lia; lia|].
    split; [rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia|]. rewrite uval_add_small by (rewrite E2; lia). lia. }
  eapply TR_pre; [|apply (REENTER_N C_nz ndZ (50, z0) (rho_sub rho s_fit)); [innthN 5 | measN]].
  intros [tr [ms md]] Hw. unfold ndZ.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc X_fit3 C_nz s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(pfit0, SLit 1)])) (NDA tv0 [] bd_nz am_nz));
    [vmr | vmr | vmr | vmr | vmr | reflexivity | vmr | vmr |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit pfit0 (SLit 1)) (fit_facts ++ ss_facts (ax_S X_fit))); [| vmr |].
  - pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model] in HJ.
    apply (JA_carve segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP pfit0 (SLit 1) X_fit rho tp (tr, mkCfg ms md));
      [vmr | reflexivity | vmr | vmr | | | exact Hw].
    + intros r HFr.
      pose proof (holds_mem _ _ (SPBranch BC_GEU vCAP (SAlu ALU_ADD vU (SLit 1))) HFr ltac:(vmr)) as G0. pose proof (holds_mem _ _ (SPUle vHD (SVar 30)) HFr ltac:(vmr)) as G3.
      pose proof (holds_mem _ _ (SPUle vU vCAP) HFr ltac:(vmr)) as G5. pose proof (holds_mem _ _ (SPUle vCAP (SLit (2 ^ 40 - 33))) HFr ltac:(vmr)) as G2.
      pose proof (holds_mem _ _ (SPUle (SVar 30) (SLit 140737479966720)) HFr ltac:(vmr)) as GT.
      zf G0. zf G3. zf G5. zf G2. zf GT. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in *. rewrite uval_lit in G2 by lia. rewrite uval_lit in GT by lia.
      pose proof (uval_range r vU). destruct (EP r ltac:(lia) G5 G2) as (E1 & _ & _ & _).
      rewrite uval_add_small in G0 by (rewrite uval_lit by lia; lia). rewrite uval_lit in G0 by lia. rewrite E1, uval_lit by lia. lia.
    + intros Ai rho1 tp1 md1 _ _ _ _ _ _.
      destruct (site_arena X_fit (removelast (ss_objs (ax_S X_fit))) X_fs0 ndO rho tp tr md HJ eq_refl HF ltac:(vmr) ltac:(vmr) ltac:(vmr)) as [SO SX].
      split.
      * intros o a Ho Hr. rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho|[<-|[]]].
        -- destruct (SO o a Ho Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold uval, vHD in *. lia.
      * change (ax_X X_fit) with ((vHD, e32 vCAP) :: X_fs0). apply xrs47_cons; [lia | exact SX].
  - intros tr' md' _ HF2. apply Forall_app. split; [|exact HF2].
    destruct (EP rho ltac:(lia) H5 H2) as (E1 & E2 & E3 & E4).
    unfold fit_facts, two40, RA.two40.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E2, ?E4, ?E3, ?E1; rewrite ?uval_lit by lia; lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
S8S150VAInv;VCST;VXGL;S6aVrho0;Se9VFB;VFF;A2VFB;VFF;S96S92S9cR1Sa5S36S0A1Sf0S131S4S4S3fZ1S5dR3S116S92PcA2A2M0A2S43G0S42Z2Z27A2A2A2S111S2eS109A1S107S118S117R3S9cR1A3S92A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr ndS] in HN, HD, HZ, HFR.
  destruct (site_rt E_m R_m tv0 rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HBf HFF HN HD HZ HFR ltac:(vmr) ltac:(vmr) ltac:(vmr)) as [A B].
  split; [exact A|]. split; [exact B|]. split; [|exact I]. change (wsub_get s_ma 12) with (SLit 65568). rewrite uval_lit by lia. lia.
Qed.
Lemma XN_E_m : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0S3fS40Z42S42Z2Z40A2A2R1A2VTR;S3aS39VJAv;Sa5A1S96R4R3A5VFAMN;R2A1A2F_;Fb;Ftp;Frho;").
Proof.
  intros rho tp b Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_ma R_m rho tp ndS bd_m (FAMN b) CMALLOC).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). vmr.
  - intros A A' _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mnull_eq. unfold ndM in REENTER_N. apply (REENTER_N T_mnull ndM (65, z0)); [innthN 3 | measN].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER_N T_mok ndMok (65, z0)); [innthN 4 | measN]].
    intros w Hw. rewrite <- T_mok_eq. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vmr.
Qed.

Lemma XN_sret : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0VTR;S3aS39VJAv;Sd9A1SccR3R2A5VFAMN;R1A1A2Fb;Ftp;Frho;").
Proof.
  intros rho tp b.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv nd1) C_1 rho' tp w)); [|apply TR_exw; intros rho'; apply C1OUT].
  intros [tr [ms md]] Hw.
  pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
  pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m (POT (SLit 1) ++ bd_rest) 0 blkN vHD (SLit 65536) (SLit 1)
                X_sret1 objsNs ohNs otNs rho tp tr ms md objsNs_eq eq_refl ltac:(vmr) ltac:(vmr) ltac:(vmr) ltac:(vmr) ltac:(vmr) ltac:(vmr) ltac:(vmr) ltac:(vmr) H1) as H2.
  rewrite X_sret2_eq in H2. cbn [remove_nth fst snd blkN tv_m] in H2. set (rho1 := rho_absorb rho [otNs] (vms md tp ms)) in H2.
  pose proof (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc X_sret2 X_sret2x s_idx
                (NDA tv0 [] (POT (SLit 1) ++ bd_rest) (AOpen (SVar pN) vHD (SLit 65536) [])) (NDA tv0 [] (POT (SLit 1) ++ bd_rest) (AOpen (SVar pN) vHD (SLit 65536) []))
                rho1 tp _ ltac:(vmr) ltac:(vmr) ltac:(vmr) ltac:(vmr) ltac:(vmr) eq_refl ltac:(vmr) ltac:(vmr) H2) as H3.
  pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] (POT (SLit 1) ++ bd_rest) bd_rest (SVar pN) vHD (SLit 65536) (SLit 1)
                X_sret2x objsNs ohNs (rho_sub rho1 s_idx) tp tr ms md objsNs2x_eq ltac:(vmr) ltac:(vmr) ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vmr) H3) as H4.
  rewrite X_sret3x_eq in H4. set (rho2 := rho_absorb (rho_sub rho1 s_idx) [ohNs] (vms md tp ms)) in H4.
  exists (rho_sub rho2 s_sretx). unfold nd1.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc X_sret3x C_1 s_sretx (NDA tv0 [] bd_rest (AHead (SVar pN) true)) (NDA tv0 [] (CHfrom 0 cs0 ++ bd_push sh_c sh_k) (AHead vHq true)));
    [vmr | vmr | vmr | vmr | vmr | reflexivity | vmr | vmr | exact H4].
Qed.

Lemma XN_nzret : ltac2:(tb__ "0|0|
S8S27S3dQ40A1A1S0VTR;S3aS39VJAv;SdcA1ScaR3R2A5VFAMN;R1A1A2Fb;Ftp;Frho;").
Proof.
  intros rho tp b.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv nd1) C_1 rho' tp w)); [|apply TR_exw; intros rho'; apply C1OUT].
  intros [tr [ms md]] Hw.
  pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HNP tv0 [] bd_nz vHD vNXl vCAPl pfit (SLit 1)
                X_nzret (objsZ ++ [ohZ]) osZ rho tp tr ms md objsZ_eq ltac:(vmr) Hw) as H2.
  rewrite X_nzret2_eq in H2. set (rho1 := rho_absorb rho [osZ] (vms md tp ms)) in H2.
  pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_nz bd_rest vHD vNXl vCAPl (SAlu ALU_ADD vUo (SLit 1))
                X_nzret2 objsZ ohZ rho1 tp tr ms md objsZ2_eq ltac:(vmr) ltac:(vmr) ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vmr) H2) as H3.
  rewrite X_nzret3_eq in H3. set (rho2 := rho_absorb rho1 [ohZ] (vms md tp ms)) in H3.
  exists (rho_sub rho2 s_nzret). unfold nd1.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc X_nzret3 C_1 s_nzret (NDA tv0 [] bd_rest (AHead vHD true)) (NDA tv0 [] (CHfrom 0 cs0 ++ bd_push sh_c sh_k) (AHead vHq true)));
    [vmr | vmr | vmr | vmr | vmr | reflexivity | vmr | vmr | exact H3].
Qed.

Lemma exits_okN : ltac2:(tb__ "0|2|
S22S45S2aS0S7A2M0S8S27S3dQ40A1A1S67S2aS2aS22S45A2M1G0A2S2bG1G0S2bS22S45R5R4A4R3A4Sd0A3VTR;S3aS39VJAv;R5A1R6R3R2A5VFAMN;S4eS2bG1G0S2bS22S45R6R5A4R4A4R3A2A1A2F_;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp Hin. cbn [In exitsN] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; destruct (edesc_eq3 _ _ _ _ _ _ H) as (<- & <- & <-).
  - apply XN_open0. measN.
  - apply XN_nohead. measN.
  - apply XN_fit. measN.
  - apply XN_nofit. measN.
  - apply XN_E_m. measN.
  - apply XN_sret.
  - apply XN_nzret.
  - apply POSTN. innth 2.
  - apply POSTN. innth 3.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S22S45S2aS0S7A2M0S8S27S3dQ40A1A1M1G1S67S2aS2aS22S45A2M2G0A2S2bG2G0S2bS22S45R6R5A4R4A4ScfA3VTR;S3aS39VJAv;R6A1R7R4R3A5VFAM;S4eS2bG2G0S2bS22S45R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. unfold exitsE, fails_t in Hin. cbn [In app] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]]];
    destruct (edesc_eq3 _ _ _ _ _ _ H) as (<- & <- & <-).
  - apply X_X_N0. measN.
  - apply X_E_ad1. measN.
  - apply X_E_ad2. measN.
  - apply X_E_ad3. measN.
  - apply X_E_ad4. measN.
  - apply X_E_vf5. measN.
  - apply X_E_vf6. measN.
  - apply X_E_vf7. measN.
  - apply X_E_vp. measN.
  - apply X_E_mk. measN.
  - apply X_E_mg. measN.
  - apply X_FL_E0.
  - apply X_FL_E1.
  - apply X_FL_50.
  - apply X_FL_51.
  - apply X_FL_60.
  - apply X_FL_61.
  - apply X_FL_70.
  - apply X_FL_71.
  - apply X_FL_p0.
  - apply X_FL_p1.
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
  - apply POST. innth 3.
Qed.
End X.

Lemma hVP_lt : (hVP < NF)%positive. Proof. reflexivity. Qed.
Lemma ndp0_none : nd_am VP.ndp0 = ANone. Proof. reflexivity. Qed.
Lemma PD_vp_none : ltac2:(tb__ "0|1|
Sf5S2aS22S45A2M0G0S3S4aS5aS37S22S45R1A3A1S57A3Ld;S85A3"). Proof. repeat constructor. Qed.
Lemma P0_vp_mono : ltac2:(tb__ "0|2|
S27S2aS0S0A2M0A1M1G1S27S2aG0S0A2A1S8G0S67G0R1R5A3S67G0R2R5A3F_;Fbn;S103R5R3R2A3S103R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S5cS39VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S10eS39S108VAInv;VCST;VXGL;A5").

Let TRs_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, triple segs ok (P a) Q) -> triple segs ok (fun w => exists a, P a w) Q
  := @triple_ex segs ok.
Lemma CMALLOC_s : ltac2:(tb__ "0|1|
Sf0S8S27S3dQ40A1A1S100S39Vok;S3aS39S10aVAInv;S2eS109A1M0S107R3VKc;S14PcA1A6S8eR2R1A5Se5S39SefR2R1S10bS108VAInv;VCST;VXGL;G0S107R3VKc;A8A5A4Ftp1;Frho1;FAi;").
Proof.
  intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc | exact (proj1 Hok) | exact (proj2 Hok)].
Qed.
Lemma CVP_s : ltac2:(tb__ "0|1|
S27S2aS0S0A2M0A1S27S2aG0S0A2A1S61S8S27S3dQ40A1A1S5fZ4R3A2S100S39Vok;S3aS39S4cVAInv;VCST;VXGL;VKc;S103R6R5A2R6R5R4S46S14aS112S29S145A3AaS8fR3R2A5Se5S39SefR3R2S126VAInv;VCST;VXGL;VKc;S103S46S149S85S112S29A3R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc VPP.P0_vp PTrue Pre_vp VP.ndp0 PD_vp NF hVP true hVP_lt ndp0_none PD_vp_none P0_vp_mono ok).
  intros FBc FFc BXc rho1 tp1 HB0. apply (VPP.vec_push_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
Qed.

Lemma MINI_s : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0SfeS8G0S100S39Vok;S3aS39VJAv;S81A1S84R2R1A5R3A4Ftp';Frho';S22S45S8G0S67S2aS22Se4A2S2bS22Se4R4SfbR3A1A4SfcA3S100S39Vok;S3aS39VJAv;R4A1R5R3R2A5R7A4F_;Ftp';Frho';Fnd;FP;S100S39Vok;S3aS39VJAv;S76A1S87R5R4A5R3A4F_;F_;FQ';Ftp;Frho;").
Proof.
  intros rho tp Q' HC1 HP.
  apply (cfg_sound_JA_h segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc ALA H_ejcert_nm_ok FUEL_fs cutpcsN NP cutsN exitsN ok Q' Hok ejcert_nm_ok) with (ndT := ndE); [|left; reflexivity].
  intros X ndX rho1 tp1 Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
  apply (exits_okN (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) TRs_exw (call_soundPA3 segs ok) CMALLOC_s
           (fun _ w => SPfamGTA segs (map nI (map edropA cutsN)) w \/ Q' w)) with (rvX := rv).
  - intros T nd rv' rho2 tp2 b HinT _. apply (reenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ok (map edropA cutsN) T nd).
    apply in_map_iff. exists (T, nd, rv'). auto.
  - intros rho2 tp2 b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HC1].
  - intros P nd rho2 tp2 b HinP. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HP; exact HinP].
  - exact Hin.
Qed.

Theorem finalize_shape_sum : ltac2:(tb__ "0|0|
S27S3dQ40A1A1S100S39Vok;S3aS39S4cVAInv;VCST;VXGL;VKc;Se9VFB;VFF;A2VFB;VFF;VBX;S46Sa2AaS9bVrho0;R1A5Se5S39S6aVrho0;R1SfcA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA_h segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc ALA H_ejcert_fs_ok FUEL_fs cutsC NP cutsE exitsE ok (Q tp0) Hok ejcert_fs_ok)
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP.arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VFZ.vec_finalizeZ_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - exact CVP_s.
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NP Kc (P0_fs FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_fs P). exact HinP.
       - intros rho1 tp1 Q' HC1 HP. exact (MINI_s rho1 tp1 Q' HC1 HP).
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S10fS39S108VAInv;VCST;VXGL;A5").

Let TRe_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, etriple segs (P a) Q) -> etriple segs (fun w => exists a, P a w) Q
  := @etriple_ex segs.
Lemma CMALLOC_e : ltac2:(tb__ "0|1|
Sf0S8S27S3dQ40A1A1SffS39S3aS39S10aVAInv;S2eS109A1M0S107R3VKc;S14PcA1A6S8eR2R1A5Se5S39SefR2R1S10bS108VAInv;VCST;VXGL;G0S107R3VKc;A8A5A3Ftp1;Frho1;FAi;").
Proof.
  intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
Qed.
Lemma CVP_e : ltac2:(tb__ "0|1|
S27S2aS0S0A2M0A1S27S2aG0S0A2A1S61S8S27S3dQ40A1A1S5fZ4R3A2SffS39S3aS39S4cVAInv;VCST;VXGL;VKc;S103R6R5A2R6R5R4S46S14aS112S29S145A3AaS8fR3R2A5Se5S39SefR3R2S126VAInv;VCST;VXGL;VKc;S103S46S149S85S112S29A3R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc VPP.P0_vp PTrue Pre_vp VP.ndp0 PD_vp NF hVP true hVP_lt ndp0_none PD_vp_none P0_vp_mono).
  intros FBc FFc BXc rho1 tp1 HB0. apply (VPP.vec_push_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
Qed.

Lemma MINI_e : ltac2:(tb__ "0|1|
S8S27S3dQ40A1A1M0SfeS8G0SffS39S3aS39VJAv;S81A1S84R2R1A5R3A3Ftp';Frho';S22S45S8G0S67S2aS22Se4A2S2bS22Se4R4SfbR3A1A4SfcA3SffS39S3aS39VJAv;R4A1R5R3R2A5R7A3F_;Ftp';Frho';Fnd;FP;SffS39S3aS39VJAv;S76A1S87R5R4A5R3A3F_;F_;FQ';Ftp;Frho;").
Proof.
  intros rho tp Q' HC1 HP.
  apply (cfg_complete_JA_h segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc ALA H_ejcert_nm_ok FUEL_fs cutpcsN NP cutsN exitsN Q' ejcert_nm_ok)
    with (ndT := ndE) (rv := (100, z0)); [|left; reflexivity].
  intros X ndX rv rho1 tp1 Hin.
  apply (exits_okN (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) TRe_exw (call_completePA3 segs) CMALLOC_e
           (fun b w => SPfamETA segs (map (enodeIA AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue) cutsN) b w \/ Q' w)).
  - intros T nd rv' rho2 tp2 b HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue cutsN T nd rv'); [exact HinT | exact Hm].
  - intros rho2 tp2 b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HC1].
  - intros P nd rho2 tp2 b HinP. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HP; exact HinP].
  - exact Hin.
Qed.

Theorem finalize_shape_sum_ex : ltac2:(tb__ "0|0|
S27S3dQ40A1A1SffS39S3aS39S4cVAInv;VCST;VXGL;VKc;Se9VFB;VFF;A2VFB;VFF;VBX;S46Sa2AaS9bVrho0;R1A5Se5S39S6aVrho0;R1SfcA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA_h segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc ALA H_ejcert_fs_ok FUEL_fs cutsC NP cutsE exitsE (Q tp0) ejcert_fs_ok)
         with (ndT := nd0) (rv := (200, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP.arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VFZ.vec_finalizeZ_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - exact CVP_e.
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NP Kc (P0_fs FB FF) FB FF BX PTrue rho0 tp0 nd Posts_fs P). exact HinP.
       - intros rho1 tp1 Q' HC1 HP. exact (MINI_e rho1 tp1 Q' HC1 HP).
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
