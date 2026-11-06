(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "bool"; "true"; "nil"; "cons"; "Some"; "fst"; "option"; "snd"; "None"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "holds"; "ss_facts"; "sobj"; "SLit"; "SPUle"; "eval"; "sprop_eqb"; "SVar"; "cell"; "ss_next"; "ss_objs"; "sv_eqb"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "frinA"; "TPA"; "tvinA"; "NDA"; "amode"; "ok_frameKA"; "fbinA"; "ffinA"; "JA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_eqs"; "PhisZ"; "z0"; "nd_e"; "gp"; "nd_ok"; "nd_p"; "cutsE"; "cutsK"; "cutsP"; "cutsS"; "ndT"; "nd_A2"; "nd_B2"; "nd_CL"; "nd_fa"; "exitsE"; "exitsK"; "exitsP"; "exitsS"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "phiK"; "efmeasA"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "xrs47_chk"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "Forall2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "JL_stack_malloc"; "J_stack_malloc_pre"; "KcA"; "Kc_ok"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "UStopLe"; "ulink"; "unwind_stopJ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "BXok_d"; "bxt"; "bitem"; "bd_wpos"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one.LI"; "P0_los"; "nd_lo0"; "Posts_loJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one"; "fr_fz"; "L_sm"; "Pre_sm"; "E_lo0"; "E_sm0"; "Fx"; "L_al"; "R_lo"; "X_rel"; "vF"; "E_lo"; "T_sm1"; "X_al"; "Xk_lo"; "ax_tidy"; "cfg_cellsE"; "cfg_cellsR"; "fnodup"; "s_lo"; "vCFG"; "xnodup"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvd"; "tnz"; "T_ok"; "remove_nth"; "tvz"; "FBx"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "nd_fz0"; "nd_fz1"; "in_lits"; "Pre_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_chk"; "extraFZ"; "xextraFZ"; "PDk_lo"; "ent_chk";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one.LD"; "NP"; "Pre_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_ad"; "vG"; "L_fr"; "Pre_fr"; "E_fa0"; "E_fd0"; "L_L1"; "L_L3"; "L_sxE"; "L_sxK"; "X_A"; "X_B"; "X_fa0"; "X_fa1"; "vNx"; "nB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xrs_okF"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2"; "P_fz"; "Posts_fz"; "P0_fz"; "fuzz_one_sumE"; "fuzz_one_sumT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_chk.K2"; "robjs_chkC"; "xrs_chkC"; "xr_inlits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_pf.Sum.X"; "extraXF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "law_flag_stmt"; "law_fshadow_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "J_free_tol_pre"; "free_tol_contract"; "free_tol_contract_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "white_hv"; "white_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_chk.HK"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_epi"; "X_ret"; "X_rl"; "K_sx"; "K_sx2"; "X_sx"; "X_sx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "site_okA"; "cmaddrA"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue"; "cell_weq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ifaceL"; "load_obj_stmtL"; "load_obj_stmt_exL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD"; "two52"; "@Stdlib.PArith.BinPos.Pos"; "add"; "lt"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_defs Lib_load_obj_p0 Lib_load_obj_iface Lib_load_obj_ifaceL Lib_load_obj_armkit2 Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2 Lib_fuzz_one_glue Lib_fuzz_one Lib_fuzz_one_ad Lib_fuzz_one_epi Lib_fuzz_one_eqs Lib_fuzz_one_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import FZAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB.
Module LG. Include Lib_load_obj_p0. End LG.

Lemma efmeas_z0 : ltac2:(tb__ "0|1|
S10S24S3SeS15S48SeS4dS1S0S0S10S24A2M0S3A2S0SeS14A2S1G0S3S1S10S24R5R4A4R3A4S1SeS14R2S36A4A4R1A2S72R2S71Z2Z40A2A2A3Frho;Fr;Fk;Fnd;FT;").
Proof. intros. unfold efmeasA, ef_rank, ef_var, z0. cbn [fst snd]. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAKT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_fuzz_one_cov.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S5aS15S2S30Q40A1A1S78OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
SeSa3VCST;R1A2S49S6eZ0R2A2S6fR2Sc7A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SeSa3VXGL;R1A2S49S6eZ0R2A2S6fR2Sc7A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SeSa6R1A1Sa3VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S0S0SeSeA2SeA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 8 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S15OFr;") := ltac2:(tb__ "0|0|
SccVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VCST;VXGL;S59VKc;Vrho0;VP0;VFB;VFF;VBX;S25Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S50VAInv;VCST;VXGL;S59VKc;Vrho0;VP0;VFB;VFF;VBX;S25VPhi;Vnd;Ad").

Lemma AGv : ltac2:(tb__ "0|0|
S15SfS14S81S59Vrho0;R3A3S48S14R2S1eR3A1A3SfaR4S59A2S48SeS7aR6R4A2S7aVrho0;R4A2A3F_;F_;F_;Fe;Fv;Frho;").
Proof using . intros rho v e Hav -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. Qed.

Lemma extraFZ_pclMA : ltac2:(tb__ "0|1|
S15S2S0S14S14A2A1S2S0S0S14SeA2S14A2A1S19SeS81S59Vrho0;R5A3VP0;Vrho0;A1S48S4Sa8R4A1S5A3S49S6eS9SeSeS23R8R5A2M0A3R4A2S6fR4SbSeSeG0A3A2A2Sc3VCST;Vrho0;Sa1VFB;R9R8A3Sc2VFF;R9R7A3R5A5F_;F_;F_;F_;Fa;Fo;Ffr;Ftv';Frho;").
Proof using .
  intros rho tv' fr o a Hav (P1 & _) HE Hr.
  apply (LG.pclMA_mono CST rho0 FB (FBx FB rho tv') FF (FFx FF rho fr) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
  unfold extraFZ in HE. apply lazy_andb_prop in HE as [Hb HE]. apply lazy_andb_prop in HE as [Hl Hh]. apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  apply P1. rewrite <- (AGv rho 12%positive vDAT Hav eq_refl ltac:(reflexivity)), <- (AGv rho 13%positive vLEN Hav eq_refl ltac:(reflexivity)).
  rewrite soff_lit_small in Hr by lia. pose proof (uval_range rho vLEN) as RL.
  assert (HL : soff rho vLEN <= uval rho vLEN).
  { unfold soff, uval. rewrite bv_signed_U. destruct (Zsigned_spec (bv_unsigned (eval rho vLEN))) as [[_ X]|[_ X]]; rewrite X; lia. }
  unfold uval in *. lia.
Qed.
Lemma xextraFZ_pclMA : ltac2:(tb__ "0|2|
S15S2S0S14S14A2M0A1S2S0S0S14SeA2S14A2A1G0SeS81S59Vrho0;R5A3VP0;Vrho0;A1S48S4Sa9R4A1S5A3S49S6eS7aR8S9S14S14R5A3A2M1R4A2S6fR4S70G1S7aR8SbS14S14R5A3A2A2A2A2Sc3VCST;Vrho0;Sa1VFB;R9R8A3Sc2VFF;R9R7A3R5A5F_;F_;F_;F_;Fa;Fr;Ffr;Ftv';Frho;").
Proof using .
  intros rho tv' fr r a Hav (P1 & _) HE Ha.
  apply (LG.pclMA_mono CST rho0 FB (FBx FB rho tv') FF (FFx FF rho fr) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
  unfold xextraFZ in HE. apply lazy_andb_prop in HE as [Hb Hl]. apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. destruct r as [rb rl]. cbn [fst snd] in Hb, Hl, Ha. subst rb rl.
  apply P1. rewrite <- (AGv rho 12%positive vDAT Hav eq_refl ltac:(reflexivity)), <- (AGv rho 13%positive vLEN Hav eq_refl ltac:(reflexivity)). exact Ha.
Qed.

Lemma fz_robjsF : ltac2:(tb__ "0|0|
S5aS15S2S16A1S2S0S14S14A2A1S2S0S0S14SeA2S14A2A1S2S19A1S15S2S30Q40A1A1S78VAInv;R9R3R2R1A4S7fS16S17R9A1R8A3VP0;Vrho0;A1S81S59Vrho0;RbA3S28Vrho0;RdA2S9eRdS5cS5bReA1A1A2S29VFB;RfReRcA4S9cRfRdA2Sa0R10ReA2S27VFF;R12R11ReA4S48S4ScfR11R10RfSa8ReA5S5A3Sc4VCST;Vrho0;VFB;VFF;R13R11R10RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (K2.robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv fr extraFZ R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraFZ_pclMA rho tv fr o a Hav HP0 HE Hr).
Qed.
Lemma fz_robjsR : ltac2:(tb__ "0|0|
S5aS15S2S16A1S2S0S14S14A2A1S2S0S0S14SeA2S14A2A1S2S19A1S15S2S30Q40A1A1S78VAInv;R9R3R2R1A4S7fS16S17R9A1R8A3VP0;Vrho0;A1S81S59Vrho0;RbA3S28Vrho0;RdA2S9eRdS5cS5bReA1A1A2S29VFB;RfReRcA4S9cRfRdA2Sa0R10ReA2S27VFF;R12R11ReA4S48S4Se1R11R10RfSa8ReA5S5A3SebVCST;Vrho0;VFB;VFF;R13R11R10RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (HK.robjs_chkR_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv fr extraFZ R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraFZ_pclMA rho tv fr o a Hav HP0 HE Hr).
Qed.
Lemma fz_xrsF : ltac2:(tb__ "0|1|
S5aS15S2S16A1S2S0S14S14A2A1M0S2S0S0S14SeA2S14A2A1G0S15S2S30Q40A1A1S78VAInv;R9R3R2R1A4S7fS16S17R9A1R8A3VP0;Vrho0;A1S81S59Vrho0;RbA3S28Vrho0;RdA2S9eRdS5cS5bReA1A1A2S29VFB;RfReRcA4S9cRfRdA2Sa0R10ReA2S27VFF;R12R11ReA4S48S4Sd0R11R10RfSa9ReA5S5A3Sc5VCST;VXGL;Vrho0;VFB;VFF;R13R11R10RfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv fr X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (K2.xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tv fr xextraFZ X rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
  intros r a Hr HE Ha. left. exact (xextraFZ_pclMA rho tv fr r a Hav HP0 HE Ha).
Qed.

Lemma site_rt : ltac2:(tb__ "0|0|
S10SafS2S19A1S15S2S0S14S14A2A1S2S0S0S14SeA2S14A2A1S2S7dA1S2bS5aS9bOF_;F_;S48S4ScfS18S11R9A1A1R5R4Sa8R7A5S5A3S48S4Sd0S18S11RaA1A1R6R5Sa9S12RaA1A5S5A3S5aS9bS7fS16S17RaA1S18S11RdA1A1A3VP0;Vrho0;A1S81S59Vrho0;RcA3S27VFF;R5RdRbA4R9R6R5A2F_;F_;F_;F_;Fms;FAi;Se8VAInv;VCST;VXGL;S59Vrho0;VP0;VFB;VFF;RcRbRaR9S2aR8R7R6R5A4ScSeA1R4AfF_;F_;F_;Fextra;Fam;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv fr bd am extra CR CX HEX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (fz_robjsF Ai rho _ tv fr R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR) as HRF.
  pose proof (fz_xrsF Ai rho _ tv fr (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX) as HXF.
  assert (HN' : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.fbinA_FBx FB Ai rho tv [] HBf HN') as FBX. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  split; [|split; [|exact (HEX Ai ms HF HP0 Hav HFR)]].
  - intros o a Ho Hr. eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact (HRF o a Ho Hr)].
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact Hc].
Qed.
Lemma payA_same : ltac2:(tb__ "0|1|
S2S16A1S2S7dA1S48S4S7eR1A1S5A3SeaS59Vrho0;VP0;R3S1aZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SeS2S30Q40A1A1S76F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S33S10S15S2S30Q40A1A1S76S7fS16S17R3A1S18S11R4A1A1A3VTR;S32S13R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S76S76S76S77R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S76OS76S77R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S33S33S10S10SafS2S19A1M0S2S0S10S5dA2M1A1S2S0S14S14A2M2A1S76S15S2S30Q40A1A1M3G2S55G2R1R5A3S55G2R2S12RbA1A3F_;Fr;S48SaG0A1S61RaR9R8A3S8G0R7A2A3S48S4S60RbRaR9R8S80G1S10S9S10S5dA2R7A4A5S5A3S15G3VTR;S32S13RfRdR2R1A5S5eS13S20S11RdA1A1R2R1RaA5A2Ftp1;Frho1;S2S79A1M4S9bS78S34S13R9R8R10S1G4Sc8R3Sc9R2R1A2A4A5R13RaR9R4R2A4R13SadSacRbRfSb0R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S10S5dG4S9bS78S15G3G4S9bS78S55G1S1S10S5dRaR9A4R14A3S34S13R12R11R19S1G4Sc8R9Sc9R8R7A2A4A5R1cR13R12RaR8A4S81S20S11R1aA1A1SadSacR14R18Sb0R9R13RaA3A3R19A2R8A3S34S13R9R8ReS1G4Sc8R7Sc9R6R5A2A4A5ReSadSacR16R1aSb0RbR15RcA3A3R1bA2R15RaR9R8R6A6S49Sf6R17Sb0RcR16RdA3R1bR1cR1dR10R1eR19RbA9S15S82R18Sb0RdR17ReA3R1cR1dS11R1eA1S11R1fA1S11R11A1R1RcA9VTR;S32S13S5fR11SadSacR19R1dSb0ReR18RfA3A3R1eA2R18RdRcA5Sf7R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S32S13R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S15OF_;S24S10S15S2S30Q40A1A1S76R6R3A1VTR;S32S13VJAv;R6A1R5R4R3A5R2A2F_;VTR;S32S13VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CSM : ltac2:(tb__ "0|2|
S5aS15S2S30Q40A1A1VTR;S32S13S65VAInv;Z2M0R3VKc;A4S88R2R1A5S5eS13S59R2R1S7S0S10S5dA2M1S1S10S5dS87S64VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CUTP : ltac2:(tb__ "0|5|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1SeG1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4S3dA3S4cS35R7R5A3S49S6eZ0S4dS1G3G0S1G2S3S1S10S24RaR9A4R8A4R7A4R6A2M4A2S6fG4R4A2A2VTR;S32S13VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Ltac meas_z0 := rewrite !efmeas_z0; vm_compute; split; [discriminate | reflexivity].

Lemma X_L_al : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2Sa4A2S8cR3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24S8cSa4A4G1A4S1SeS14Z3e7S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_al as (_ & CF & CLF & CFb & _ & _ & _ & _ & Cx1 & Co1 & Cw1 & Cx2 & Co3 & Cw3 & CHF & CHA & Cx3 & _).
  pose proof fz_chk_al as C1. apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_fz0) C_al (rho_sub rho s_al) tp)).
  { intros w Hw.
    assert (Hw1 : SPA segs (JAv nd_fz0) L_alF rho tp w).
    { rewrite <- CLF. apply (SPA_refacts segs _ rho L_al _ tp w Hw CFb). intros HF. apply Forall_app. split; [|exact HF].
      apply al_facts_hold. rewrite <- CF. exact HF. }
    pose proof (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc L_alF C0 s_al nd_fz0 nd_fz0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw1) as Hw2.
    pose proof (SPA_axforms segs _ xf_al1 (rho_sub rho s_al) C0 C1 tp w Cx1 Hw2) as Hw3.
    assert (Hw4 : SPA segs (JAv nd_fz0) C2 (rho_sub rho s_al) tp w).
    { unfold C2. apply (SPA_reshape segs _ (rho_sub rho s_al) C1 0 _ oM0 tp w Co1); [reflexivity | reflexivity | reflexivity | exact Cw1 | | exact Hw3].
      intros _. split; reflexivity. }
    pose proof (SPA_axforms segs _ xf_al2 (rho_sub rho s_al) C2 C3 tp w Cx2 Hw4) as Hw5.
    assert (Hw6 : SPA segs (JAv nd_fz0) C4 (rho_sub rho s_al) tp w).
    { unfold C4. apply (SPA_reshape segs _ (rho_sub rho s_al) C3 0 _ oH tp w Co3); [reflexivity | reflexivity | reflexivity | exact Cw3 | | exact Hw5].
      intros HF. pose proof (has_facts_sound _ _ _ HF CHF) as HF1. pose proof (has_facts_sound _ _ _ HF CHA) as HF2.
      unfold oH, oBack, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
      pose proof (al_lo _ HF1 HF2) as E1. pose proof (al_hi _ HF1 HF2) as E2. unfold uval in E1, E2. rewrite soff_lit_small by lia. lia. }
    exact (SPA_axforms segs _ xf_al3 (rho_sub rho s_al) C4 C_al tp w Cx3 Hw6). }
  apply (CUTP C_al nd_fz0 0%nat (990, z0) (rho_sub rho s_al) tp); [right; left; reflexivity | exact I | meas_z0].
Qed.

Definition extraXF (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S4S4L_;Sa9Vr;A1S5Sd1Vr;A1X4x2").
Lemma fz_xrsL : ltac2:(tb__ "0|4|
S5aS15S2S16A1S2S0S14S14A2A1M0S2S0S0S14SeA2S14A2M1A1M2SaS3A1M3S2S19A1G0S15S2S30Q40A1A1S78VAInv;RbR3R2R1A4S7fS16S17RbA1RaA3VP0;Vrho0;A1S81S59Vrho0;RdA3S28Vrho0;RfA2S9eRfS5cS5bR10A1A1A2S29VFB;R11R10ReA4S9cR11RfA2Sa0R12R10A2S27VFF;R14R13R10A4S48S4Sd4VXGL;R13R12R11R10RfSd2ReA8S5A3Sc6VCST;VXGL;Vrho0;VFB;VFF;R15R13G3G2Lskip;R11S3S9fG1R1R13A3Li;R12Xax2RfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR Hchk.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraXF X rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hchk).
  intros r a Hr HE Ha. unfold extraXF in HE. apply lazy_orb_prop in HE as [HE|HE].
  - left. exact (xextraFZ_pclMA rho tv _ r a Hav HP0 HE Ha).
  - right. apply HXlits. exact (K2.xr_inlits_sound r rho a HE Ha).
Qed.
Lemma CXL_sm : ltac2:(tb__ "0|0|
S48S4Sd4VXGL;S8bS91A1S6S0S14S14A2A1S86S8S3U0A2S6S19A1Sd2S92A8S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma xnodup_incl : ltac2:(tb__ "0|1|
S2S0S14S14A2M0A1G0S55G0R1S9aR2A1A3S55G0R2R3A3F_;Fr;Fl;").
Proof using .
  induction l as [|x l IH]; intros r H; cbn in H; [exact H|].
  destruct (existsb _ l); [right; exact (IH r H)|]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH r H)].
Qed.
Lemma fnodup_incl : ltac2:(tb__ "0|0|
S2S16A1S16S55S16R1S97R2A1A3S55S16R2R3A3F_;Ff;Fl;").
Proof using .
  induction l as [|x l IH]; intros f H; cbn in H; [exact H|].
  destruct (existsb _ l); [right; exact (IH f H)|]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH f H)].
Qed.
Lemma SPA_tidy : ltac2:(tb__ "0|0|
S33S15S10S2S30Q40A1A1S77S32S13R5R3R4R2R1A6S32S13R6S94R4A1R5R3R2A6F_;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w H. unfold ax_tidy.
  pose proof (SPA_x_sub segs J rho A (xnodup (ax_X A)) tp w (xnodup_incl _) H) as H1.
  apply SPA_refacts; [exact H1 | |].
  - destruct w as [tr [ms md]]. destruct H1 as [(Hsm & _) _]. destruct Hsm as [Hwf _].
    unfold swf in Hwf. repeat (apply andb_prop in Hwf as [Hwf ?X]).
    apply forallb_forall. intros f Hf. apply (proj1 (forallb_forall _ _) X f (fnodup_incl _ f Hf)).
  - intros HF. apply Forall_forall. intros f Hf. exact (proj1 (Forall_forall _ _) HF f (fnodup_incl _ f Hf)).
Qed.

Lemma X_E_sm0 : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2Sa4A2S8aR3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24S8aSa4A4G1A4S1SeS14Z3ddS36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_sm as (_ & Cent & Cchk & Cta & Cnp & C12 & CT & Csel & Cobjs & CX & Cnx & Copen & CCpro & _).
  pose proof fz_chk_sm as (CR & CXr & Cnb & Cwp & CvR & CpR & CvF & CpF & Cbase & Cswf & Cnp1 & Cnb1 & _ & Cal & CpFn).
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           2 E_sm0 s_sm R_sm rho tp nd_fz0 pF pFL _ CSM).
  - lia.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cwp.
  - exact CvR.
  - exact CpR.
  - exact CvF.
  - exact CpF.
  - intros A A' _; exact I.
  - apply (site_rt E_sm0 s_sm R_sm rho [] [] bd_fz ANone _ CR CXr).
    intros Ai ms HF HP0 Hav HFR. split.
    + rewrite C12. rewrite uval_lit by lia. change (fs_frame_size 2) with 256. lia.
    + destruct HP0 as (_ & HC0 & _). unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  - intros rho' tp'. change (T_afterA (Pre_stack_malloc AE_A 2) E_sm0 s_sm R_sm (L_stack_malloc AE_A 2)) with (T_afterA Pre_sm E_sm0 s_sm R_sm L_sm). rewrite CT.
    cbn [nd_tv nd_fr nd_bd nd_am nd_fz0].
    eapply TR_pre with (P := SPA segs (JAv nd_p) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w Csel Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_p) C_pro rho2 tp' w)).
    { intros w Hw. unfold nd_p.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
                  [] fr_fz bd_fz ANone 0%nat pF 2 pFL T_sm1 objs_sm1 X_al [] rho' tp' w eq_refl ltac:(lia) Cbase Cobjs CX
                  Cswf Cnp1 Cnb1) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (fz_xrsL Ai rho' _ [] fr_fz (Some 0%nat) [] X_al rho1 tp1 md1 HM HF2 HP0 Hav HT HTK HN HDt HZt HFR CXL_sm).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite Copen in Hw2. rewrite <- CCpro.
        apply (SPA_x_len0 segs (JAv (NDA [] fr_fz bd_fz ANone)) C_pro0 pF 5 rho2 tp' w); [exact Cal | lia | exact CpFn | exact Hw2]. }
    apply TR_exw. intros rho2. apply (CUTP C_pro nd_p 0%nat (980, z0) rho2 tp'); [right; right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma f32_rng : ltac2:(tb__ "0|0|
S15S2S16A1S7fS16S17R2A1R1A3S48S4S56S16S1dS1bS8fS1aS73Z7fffff800000Z100A2A1A2A1R2A3S5A3S48SeS7aR4S99A2S70S7aR4S8fA2Z20A2A3F_;F_;FF;Fr;").
Proof using .
  intros r F HF Hm. pose proof (holds_mem _ _ _ HF Hm) as A. apply (proj1 (h_ule _ _ _)) in A. rewrite uval_lit in A by lia.
  pose proof (uval_range r vF). unfold vCFG. apply uval_addk. lia.
Qed.

Lemma X_X_rel : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S3aA2S8eR3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24S8eS3aA4G1A4S1SeS14Z3d3S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_sm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cobjs & Clocal & CCms).
  pose proof fz_chk_rel as (Cbase & Chf & Cnb & CRR & Cf32 & _).
  pose proof fz_checks_ms as (Cxf & Co2 & Cwf & CEms & _ & Cbody & Cxfb & _).

  apply (TR_pre (fun w => exists rho', SPA segs (JAv nd_p) C_ms rho' tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj gF 0 32 cells_rel DZero] (vms md tp ms)). rewrite <- CCms. unfold nd_p.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] fr_fz bd_fz ANone 0%nat pF 2 pFL gF 0 32 cells_rel DZero X_rel objs_rel [(32, 144)] rho tp tr ms md
             eq_refl ltac:(lia) Cbase Cobjs ltac:(lia) ltac:(vm_compute; split; discriminate) eq_refl Chf Clocal Cnb); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (fz_robjsR Ai rho _ [] fr_fz objs_rel rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CRR). }
  apply TR_exw. intros rho'.

  eapply TR_pre; [|apply (CUTP C_body nd_p 0%nat (970, z0) rho' tp); [right; right; right; left; reflexivity | exact I | meas_z0]].
  intros w Hw. pose proof (SPA_axforms segs _ xf_ms rho' C_ms C_ms1 tp w Cxf Hw) as Hw1.
  assert (Hw2 : SPA segs (JAv nd_p) E_ms rho' tp w).
  { rewrite <- CEms.
    apply (SPA_reshape segs _ rho' C_ms1 2 _ _ tp w Co2); [reflexivity | reflexivity | reflexivity | exact Cwf | | exact Hw1].
    intros HF. unfold cfg_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho' vCFG)) with (uval rho' vCFG). rewrite (f32_rng rho' _ HF Cf32). unfold uval. lia. }
  rewrite <- Cbody. apply SPA_tidy. exact (SPA_axforms segs _ xfb_ms rho' E_ms _ tp w Cxfb Hw2).
Qed.

Hypothesis CLO : ltac2:(tb__ "0|1|
S2S0SeSeA2M0A1S2S0G0SeA2A1S7cS15S2S30Q40A1A1S7bZ7R3A2VTR;S32S13S26VAInv;VCST;VXGL;VKc;S83VCST;R6R5A3R6R5R4S25S84AaSb2R3R2A5S5eS13Sb1R3R2Sd3VAInv;VCST;VXGL;VKc;S83VCST;A1S25SaaR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTS : ltac2:(tb__ "0|5|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1SeG1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4S3eA3S4cS35R7R5A3S49S6eZ0S4dS1G3G0S1G2S3S1S10S24RaR9A4R8A4R7A4R6A2M4A2S6fG4R4A2A2VTR;S32S13VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUTE : ltac2:(tb__ "0|5|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1SeG1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4S3bA3S4cS35R7R5A3S49S6eZ0S4dS1G3G0S1G2S3S1S10S24RaR9A4R8A4R7A4R6A2M4A2S6fG4R4A2A2VTR;S32S13VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma HIN_lo : ltac2:(tb__ "0|3|
S15S9bS5aS15S2S30Q40A1A1S78S7fS16S17R6A1S18S11S90A1A1A3VP0;Vrho0;A1S81S59Vrho0;R8A3VAInv;R7R6R5R4A4S28Vrho0;R8A2S9eRbS5cS5bR9A1A1A2S2dVFB;RaA2S2eVFF;RbA2S29VFB;RcReSdS0S14S14A2M0S6G0A1M1G1A3M2A4S9cRfG2A2Sa0R10G2A2S27VFF;RfR11S86A4S49Sc4VCST;Vrho0;VFB;VFF;R12G1S86S8dA8S49Sc5VCST;VXGL;Vrho0;VFB;VFF;R12G1S86S93A9S83VCST;Sa1VFB;R12G1A3Sc2VFF;R12S86A3SadSacR12S8dR11A3S98A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [app] in HN, HD, HZ.
  pose proof fz_chk_lo as (CR & CX & _ & _ & _ & _ & _ & _ & _ & _ & C13 & C14 & C15 & C28 & Cf32 & CHF & CHA & _).
  pose proof fz_checks_lo as (_ & _ & _ & _ & _ & _ & _ & _ & Cta & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split].
  - exact (fz_robjsF Ai rho _ [] fr_fz R_lo rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
  - exact (fz_xrsF Ai rho _ [] fr_fz Xk_lo rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX).
  - pose proof HP0 as (Ptxt & Pcen & _).
    pose proof (f32_rng rho _ HF Cf32) as Ecfg.
    pose proof (holds_mem _ _ _ HF Cf32) as HvF. apply (proj1 (h_ule _ _ _)) in HvF. rewrite uval_lit in HvF by lia.
    assert (HinF : In (uval rho vF, fs_frame_size 2, uval rho vFL) (FFx FF rho fr_fz)).
    { apply In_FFx. right. exists (vF, 2, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 2) with 256 in HinF.
    pose proof (has_facts_sound _ _ _ HF CHF) as HFz.
    pose proof (fz_S rho HFz) as (_ & AS & BS). pose proof (U_win rho HFz) as (_ & _ & TW). pose proof (fz_D rho HFz) as AD.
    pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
    assert (ET : uval rho vTOPfz = T0 rho0) by (destruct HT0 as [E _]; exact E).
    unfold LI.P0_los, LG.P0_lo, uval, LD.vBUF, LD.vLEN, LD.vCFGp. cbn [eval]. rewrite !rw_call'. rewrite C13, C14, C15, C28.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    split; [split; [|split]|split].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NF rho0 s_lo rho R_lo ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho []) (FFx FF rho fr_fz) a).
      apply (LG.pclMA_mono CST rho0 FB (FBx FB rho []) FF (FFx FF rho fr_fz) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AGv rho 12%positive vDAT Hav eq_refl ltac:(reflexivity)), <- (AGv rho 13%positive vLEN Hav eq_refl ltac:(reflexivity)). exact Ha.
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. right; right; right. exists (uval rho vF), 256, (uval rho vFL). split; [exact HinF|]. lia.
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. left. rewrite (T0_calleeA NF rho0 s_lo rho R_lo ms Hav Cta). rewrite <- ET. lia.
    + exists (uval rho vF), 256, (uval rho vFL). split; [exact HinF|]. lia.
    + intros c Hc. unfold FFx. rewrite map_app, ccount_app. rewrite (Pcen c). cbn [map fst snd fr_fz frv plus].
      unfold LI.lo_classes in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
Qed.

Lemma recell_cfg : ltac2:(tb__ "0|0|
S15S58S1fS1fSefR1A1S95S96A5Frho;").
Proof using .
  intros rho. unfold cfg_cellsE, cfg_cellsR. constructor; [|constructor; [apply cell_weq_refl | constructor]].
  apply cell_weq_lit. reflexivity.
Qed.

Lemma X_E_lo0 : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S3aA2S89R3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24S89S3aA4G1A4S1SeS14Z3c9S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_lo as (_ & Cxf & Co8 & Cwf8 & CElo & _ & Cent & Cchk & Cta & Cdom & Cnp & _ & _ & Czf & CElo2 & Cswf2 & CTe & CTo & Co2 & Cwf2 & CTe1 & Cxe & Cte & _ & Cxo & Cto & _).
  pose proof fz_chk_lo as (_ & _ & Cxk & Cnb & Cbr & Ctvs & Cam & Chand & Cwp & Cpd & _ & _ & _ & _ & _ & _ & _ & Etv & Ebd & Eam & Otv & Obd & Oam).
  apply (TR_pre (SPA segs (JAv (NDA ([] ++ []) fr_fz bd_fz ANone)) E_lo rho tp)).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_lo rho E_lo0 E_lo1 tp w Cxf Hw) as Hw1. rewrite <- CElo.
    pose proof (SPA_zero_fill segs _ rho E_lo1 8 _ tp w Czf Cswf2 Hw1) as Hw2. rewrite CElo2 in Hw2.
    exact (SPA_recell segs _ rho E_lo2 8 _ cfg_cellsR tp w Co8 Cwf8 (fun _ => recell_cfg rho) Hw2). }
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX (LI.P0_los CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           LD.Pre_lo LI.nd_lo0 PDk_lo LD.NP eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CLO eq_refl
           E_lo s_lo R_lo Xk_lo rho tp [] [] fr_fz bd_fz [] ANone _
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply payA_same. exact Cwp.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_lo rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndLd] PsiL] rho' tp' Hd Hag HK _.
    cbn [PDk_lo liftPD LI.PD_lo map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      fold isub_err. rewrite Etv, Ebd, Eam, CTe.
      apply (TR_pre (SPA segs (JAv nd_e) T_err rho' tp')).
      { intros w Hw. rewrite <- Cte. apply SPA_tidy. apply (SPA_axforms segs _ xfb_err rho' T_err1 _ tp' w Cxe). rewrite <- CTe1.
        apply (SPA_reshape segs _ rho' T_err0 2 _ out_mid tp' w Co2); [reflexivity | reflexivity | reflexivity | exact Cwf2 | | exact Hw].
        intros HF. unfold out_mid, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
        change (bv_unsigned (eval rho' (hp 16))) with (uval rho' (hp 16)). unfold hp.
        assert (HA : Forall (holds rho') (al_facts vH vDN vG10)).
        { apply (has_facts_sound _ _ _ HF). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }
        assert (HFz : Forall (holds rho') fz_facts).
        { apply (has_facts_sound _ _ _ HF). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }
        pose proof (al_H rho' HA) as AH. pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
        rewrite uval_addk by lia. unfold uval. lia. }
      apply (CUTE T_err nd_e 0%nat (400, z0) rho' tp'); [left; reflexivity | exact I | meas_z0].
    +
      fold isub_ok. rewrite Otv, Obd, Oam, CTo.
      apply (TR_pre (SPA segs (JAv nd_ok) T_suc rho' tp')).
      { intros w Hw. rewrite <- Cto. apply SPA_tidy. exact (SPA_axforms segs _ xfb_ok rho' T_suc0 _ tp' w Cxo Hw). }
      apply (CUTS T_suc nd_ok 0%nat (600, z0) rho' tp'); [left; reflexivity | exact I | meas_z0].
Qed.

Hypothesis CFREE : ltac2:(tb__ "0|1|
S5aS15S2S30Q40A1A1VTR;S32S13Sd7S13VAInv;R3VKc;A4Sb5R2R1A5S5eS13S59R2R1S7S0S10S5dA2M0S1S10S5dSb4S63VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CUTK : ltac2:(tb__ "0|5|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1SeG1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4S3cA3S4cS35R7R5A3S49S6eZ0S4dS1G3G0S1G2S3S1S10S24RaR9A4R8A4R7A4R6A2M4A2S6fG4R4A2A2VTR;S32S13VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma popN_site : ltac2:(tb__ "0|1|
S2S0S14S14A2A1S2S7dA1S2bS10S15S2S30Q40A1A1S77S32S13VJAv;S2aR7S86R6R5A4A1R4R3R2R1A6S48S4Se1S18S11R5A1M0A1R8S86Sa8S21G0A1A5S5A3S48S4S54S18S11R6A1A1R9S12R6A1A3S5A3S49SebVCST;Vrho0;VFB;VFF;R6RaS86S21S11R7A1A1A8SecR6S12R7A1A2A2F_;F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ftv;").
Proof using ALA HCST.
  intros tv bd am A rho tp [tr [ms md]] [Hsm (Ai & kc & HJ)] CR CX.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & _). cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  pose proof (T_of_TPA NF rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
  split.
  - exact (fz_robjsR Ai rho _ tv fr_fz _ rho tp md HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
  - exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai rho _ tv _ rho tp md HM HF HN HZ CX).
Qed.

Lemma gp_val : ltac2:(tb__ "0|0|
S15S14SeS2S16A1S7fS16S17R4A1R1A3S48S4S56S16S1dS1bR4S1aSf8A1A2A1R2A3S5A3S49S6eZ0R4A2S6fR4Z1000A2A2S48SeS31Q40S1cR7S38R6R5A2A2A2S70S7aR7R6A2R5A2A3F_;F_;F_;Ffacts;Fk;Fg;Frho;").
Proof using .
  intros rho g k facts HF C Hk. pose proof (holds_mem _ _ _ HF C) as H. apply (proj1 (h_ule _ _ _)) in H. rewrite uval_lit in H by (unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52; lia).
  unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52 in H. pose proof (uval_range rho g) as R.
  change (bv_unsigned (eval rho (gp g k))) with (uval rho (gp g k)). unfold gp. apply uval_addk. lia.
Qed.
Lemma gp_val' : ltac2:(tb__ "0|0|
S15S14SeS6eS7aR3R2A2S71Z2Z34A2A2S49S6eZ0R2A2S6fR2Z1000A2A2S48SeS31Q40S1cR5S38R4R3A2A2A2S70S7aR5R4A2R3A2A3F_;F_;Fk;Fg;Frho;").
Proof using .
  intros rho g k H Hk. pose proof (uval_range rho g) as R. change (bv_unsigned (eval rho (gp g k))) with (uval rho (gp g k)). unfold gp. apply uval_addk. lia.
Qed.
Lemma efmeas_gp : ltac2:(tb__ "0|2|
S10S24S3SeS14SeS15S48SeS4dS1S0S0S10S24A2M0S3A2S0SeS14A2S1G0S3S1S10S24R7R6A4R5A4S1SeS14R4S38R3R2A2M1A4A4R1A2S70S72R4S71Z2Z40A2A2S31Q40S1cR1G1A2A2A2A3Frho;Fc;Fg;Fr;Fk;Fnd;FT;").
Proof using . reflexivity. Qed.

Lemma X_X_fa0 : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S39A2SbeR3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24SbeS39A4G1A4S1SeS14Z257S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_chk_loop as (C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof fz_checks_fa as (_ & _ & _ & _ & _ & Cz & _).
  apply (TR_pre (SPA segs (JAv nd_fa) K_fa (rho_sub rho s_fa0) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_fa0 K_fa s_fa0 nd_fa nd_fa rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (JA_head0_none segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue HBX tvA fr_fz KU1 pH false X_fa0 rho tp w Cz Hw). }
  apply (CUTK K_fa nd_fa 0%nat (450, z0) (rho_sub rho s_fa0) tp); [left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_X_fa1 : ltac2:(tb__ "0|4|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S3fSc0Sb3A2M2A2SbfR3R2A5VFAM;S4dS1S0S0S10S24A2M3S3A2S0SeS14A2S1G3S3S1S10S24SbfG2A4G1A4S1SeS14Z1f3S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_chk_loop as (_ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof fz_checks_fa as (_ & _ & _ & _ & _ & _ & Cz & _).
  apply (TR_pre (SPA segs (JAv nd_fa) K_fa (rho_sub rho s_fa1) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_fa1 K_fa s_fa1 nd_fa nd_fa rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (JA_headN_none segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue HBX tvA fr_fz KU1 vNx vG X_fa1 rho tp w Cz Hw). }
  apply (CUTK K_fa nd_fa 0%nat (450, z0) (rho_sub rho s_fa1) tp); [left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_X_A : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S39A2SbcR3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24SbcS39A4G1A4S1SeS14Z257S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_chk_loop as (_ & _ & _ & _ & CnpA & CnbA & CnpA1 & CnbA1 & CR & CX & Cnd & _).
  pose proof fz_checks_loop1 as (_ & _ & _ & ClenN & CwfA1 & Cpop & CwfA2 & CbaseA1 & Chnz & _).
  apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_A2) X_A2 rho2 tp w)).
  { intros w Hw.
    destruct (JA_lenN segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue HBX ALA HKc tvA fr_fz KU1 pH false X_A rho tp w ltac:(rewrite ClenN; exact CwfA1) CnpA CnbA Hw) as (rho1 & _ & Hw1).
    rewrite ClenN in Hw1. fold gA in Hw1.
    destruct (JA_popN segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue HBX ALA HCST HXGL HKc HNP tvA fr_fz KU1 pH gA X_A1 rho1 tp w ltac:(rewrite Cpop; exact CwfA2) CbaseA1 CnpA1 CnbA1 Chnz
                ltac:(intros; exact (popN_site tvA KU1 (AHeadN pH gA) X_A1 rho1 tp w Hw1 CR CX)) Hw1) as (rho2 & _ & Hw2 & _).
    exists rho2. rewrite Cpop in Hw2. unfold nx in Cnd. rewrite Cnd in Hw2. exact Hw2. }
  apply TR_exw. intros rho2.
  apply (CUTS X_A2 nd_A2 0%nat (590, z0) rho2 tp); [right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_L_L1 : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S40A2Sb8R3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24Sb8S40A4G1A4S1SeS14Z24dS36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_chk_loop as (_ & _ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_CL) C_L (rho_sub rho s_L1) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc L_L1 C_L s_L1 nd_A2 nd_CL rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUTS C_L nd_CL 0%nat (500, gp vG 8) (rho_sub rho s_L1) tp); [right; right; left; reflexivity | exact I |].
  rewrite efmeas_z0, efmeas_gp. pose proof (bv_urange (eval (rho_sub rho s_L1) (gp vG 8))) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Lemma X_L_L3 : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S41A2Sb9R3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24Sb9S41A4G1A4S1SeS14Z1f4S38S1eSf9Sc1P3A2A1ZbA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_chk_loop as (_ & _ & _ & C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FgL & Csub). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply TR_facts. intros HF.
  apply (TR_pre (SPA segs (JAv nd_CL) C_L (rho_sub rho s_L3) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc L_L3 C_L s_L3 nd_B2 nd_CL rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUTS C_L nd_CL 0%nat (500, gp vG 8) (rho_sub rho s_L3) tp); [right; right; left; reflexivity | exact I |].
  rewrite !efmeas_gp. rewrite <- (eval_subst rho s_L3 (gp vG 8)), Csub.
  rewrite (gp_val rho (SVar (nB + 3)) 8 _ HF FgL) by lia. rewrite (gp_val rho (SVar (nB + 3)) 11 _ HF FgL) by lia.
  pose proof (uval_range rho (SVar (nB + 3))) as R. lia.
Qed.

Lemma tvd_nth_remove : ltac2:(tb__ "0|1|
S15S2S0S14S14A2M0A1S3G0G0S9cR5R4A2S48SaG0A1S57G0R5R4A3S8G0R3A2A3S55G0R3S9fG0R5R6A3A3S9dR8R5A2S9dR9R5A2S4bS48S0SeSeA2Sa2RaR7A2Sa2RaR6A2A3A1F_;F_;F_;F_;F_;Ft';Ft;Fi;Ftv;Frho;").
Proof using .
  intros rho tv. induction tv as [|h r IH]; intros [|i] t t' HD Hn Hin Hz Hz'; cbn in Hn, Hin; try discriminate; try contradiction.
  - injection Hn as ->. destruct HD as [H _]. exact (H t' Hin Hz Hz').
  - destruct HD as [H HD']. destruct Hin as [<-|Hin].
    + intros E. exact (H t (nth_error_In _ _ Hn) Hz' Hz (eq_sym E)).
    + exact (IH i t t' HD' Hn Hin Hz Hz').
Qed.

Lemma pclMA_cmaddrA_x : ltac2:(tb__ "0|1|
S5aS15S2S0S14S14A2M0A1S2S0S0S14SeA2S14A2A1S3G0SeS15S2S30Q40A1A1S78VAInv;RaR3R2R1A4S2dVFB;RbA2S2eVFF;RcA2S28Vrho0;RdA2S29VFB;ReRdRcA4S9cReRdA2S27VFF;R10RfRdA4S48SaG0A1S57G0RfRdA3S8G0RcA2A3S9dR11RdA2Sc3VCST;Vrho0;Sa1VFB;R12S9fG0RfR11A3A3Sc2VFF;R12R10A3RdA5Se9VCST;R14S8SeS9SeSeSa2R13RfA2A3A2ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;Fa;Ft;Fi;Ffr;Ftv;Frho;FAi;").
Proof using ALA.
  intros Ai rho tv fr i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hz Hp.
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
    destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.ffinA_FFx FF Ai rho fr HFF HFR f s fl Hin) as [H _]. split; [exact H | exact Hr].
Qed.

Lemma site_free : ltac2:(tb__ "0|3|
S10SafS2S19A1S15S2S0S14S14A2M0A1S2S0S0S14SeA2S14A2A1S3G0S2S7dA1S2bS48SaG0A1S57G0R6R4A3S8G0R3A2A3S48S4ScfS18S11RbA1A1S9fG0R5R7A3R6Sa8R9A5S5A3S48S4Sd0S18S11RcA1A1S9fG0R6R8A3R7Sa9S12RcA1A5S5A3S48S4S22S9S14S14R6A3SaeRcPcM1A2A2S5A3S48S4S22SbS14S14R7A3SaeRdPdM2A2A2S5A3S7fS16S17RcA1S18S11RfA1A1A3S9dRdR9A2F_;Se8VAInv;VCST;VXGL;S59Vrho0;VP0;VFB;VFF;R10RfReRdS2aRcRbR8R7A4S8SeS7aRdSaeRfG1A2A2A2S5aS9bS49S9dRfRbA2S49S48S0SeSeA2Sa2RfRbA2S1SeSeS7aRfSaeR11G1A2A2S7aRfSaeR11G2A2A2A4A3S6dS6S6cA1S6bSadSacRfR10R1A3R11A2A3A2A2Lms;LAi;AfF_;F_;F_;F_;F_;F_;Fam;Fbd;Ft;Fi;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv fr i t bd am Hn CR CX H12 H13 Hnzf Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13. rewrite <- H12, <- H13.
  pose proof (Hnzf HF) as Hnz.
  assert (HNr : tvinA FB Ai rho (remove_nth i tv)) by (apply (tvinA_sublist FB Ai rho tv); [intros x Hx; exact (remove_nth_In _ _ _ Hx) | exact HN]).
  assert (HDr : tvd rho (remove_nth i tv)) by (apply tvd_remove; exact HD).
  assert (HZr : tvz rho (remove_nth i tv)) by (apply (tvz_sublist rho tv); [intros x Hx; exact (remove_nth_In _ _ _ Hx) | exact HZ]).
  pose proof (fz_robjsF Ai rho _ _ fr R rho1 tp1 md1 HM HF HP0 Hav HT HTK HNr HDr HZr HFR CR) as HRF.
  pose proof (fz_xrsF Ai rho _ _ fr (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HNr HDr HZr HFR CX) as HXF.
  split; [|split; [|split; [exact Hnz | split; [reflexivity | exact I]]]].
  - intros o a Ho Hr. exact (pclMA_cmaddrA_x Ai rho tv fr i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hnz (HRF o a Ho Hr)).
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    exact (pclMA_cmaddrA_x Ai rho tv fr i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hnz Hc).
Qed.

Lemma X_E_fd0 : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S42A2Sb7R3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24Sb7S42A4G1A4S1SeS14Z1f4S38Sb3Z7A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_fd as (_ & Cxf & CdX & CwfE & Cent & Cchk & Cta & Cnp & C12 & C13 & CT0 & Cxb & Ctidy & CwfT & _).
  pose proof fz_chk_fd as (CR & CX & Fnz & Cpay & Cbb & Cnb & Fg & Cgb).
  apply (TR_pre (SPA segs (JAv nd_CL) E_fd rho tp)).
  { intros w Hw. rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0)|].
    exact (SPA_axforms segs (JAv nd_CL) (xf_fd E_fd0) rho E_fd0 E_fd1 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (TobjJAKT.free_tol_callT_k segs AE_A AInv CST XGL ALA HCST HXGL HTOP NF Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           E_fd s_fd R_fd rho tp nd_CL 0%nat (vNd, e32 vCap) KU1 _ CFREE
           Cent Cchk Cta Cnp Cnb Cbb eq_refl).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fd s_fd R_fd rho ((vNd, e32 vCap) :: tvA) fr_fz 0%nat (vNd, e32 vCap) (KU1 ++ [BIc 0 1 KU]) (AHeadN vNx vG) eq_refl);
      [exact CR | exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. pose proof (holds_mem _ _ _ HFE Fnz) as Hd. apply (proj1 (holds_nbeq _ _ _)) in Hd.
    change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in Hd. rewrite uval_lit in Hd by lia. exact Hd.
  - intros HP0. exact (proj2 (proj2 HP0)).
  - intros HFc Hagc. exact (Lib_fuzz_one_cov.cov_sound E_fd s_fd R_fd rho0 rho Lib_fuzz_one_cov.cov_fd HFc Hagc).
  - intros rho' tp' Hag _. cbn [nd_tv nd_fr nd_am nd_CL ndN remove_nth]. unfold Pre_fr, L_fr in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv (ndT vNx vG)) T_fd rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs _ xfb_fd rho' T_fd0 _ tp' w Cxb Hw). }
    apply (CUTS T_fd (ndT vNx vG) 0%nat (500, gp vG 6) rho' tp'); [right; right; right; left; reflexivity | exact I |].
    rewrite !efmeas_gp. rewrite <- (eval_agree_vals _ rho rho' (gp vG 6) Hag Cgb).
    rewrite (gp_val rho vG 6 _ HF Fg) by lia. rewrite (gp_val rho vG 7 _ HF Fg) by lia.
    pose proof (uval_range rho vG) as R. lia.
Qed.

Lemma X_X_B : ltac2:(tb__ "0|4|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S3fSc0Sb3A2M2A2SbdR3R2A5VFAM;S4dS1S0S0S10S24A2M3S3A2S0SeS14A2S1G3S3S1S10S24SbdG2A4G1A4S1SeS14Z1f4S38Sb3Z5A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_chk_loop as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CnpB & CnbB & CRB & CXB & CndB & CnB & FgB & _ & _).
  pose proof fz_checks_fd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fnz & Cpop & CwfB2 & CbaseB & _).
  apply TR_facts. intros HF.
  pose proof (holds_mem _ _ _ HF FgB) as HgB. apply (proj1 (h_ule _ _ _)) in HgB. rewrite uval_lit in HgB by (unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52; lia). unfold two52, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52 in HgB.
  apply (TR_pre (fun w => exists rho2, (bv_unsigned (rw rho2 (nB + 3)%positive) + 16 = uval rho vG) /\ SPA segs (JAv nd_B2) X_B2 rho2 tp w)).
  { intros w Hw.
    destruct (JA_popN segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue HBX ALA HCST HXGL HKc HNP tvA fr_fz KU1 vNx vG X_B rho tp w ltac:(rewrite Cpop; exact CwfB2) CbaseB CnpB CnbB Fnz
                ltac:(intros; exact (popN_site tvA KU1 (AHeadN vNx vG) X_B rho tp w Hw CRB CXB)) Hw) as (rho2 & _ & Hw2 & Hg).
    exists rho2. unfold nx in CnB, CndB. rewrite CnB in Hg. split; [exact Hg|]. rewrite Cpop in Hw2. rewrite CndB in Hw2. exact Hw2. }
  apply TR_exw. intros rho2.
  apply (TR_pureP _ (bv_unsigned (rw rho2 (nB + 3)%positive) + 16 = uval rho vG)); [intros w [H _]; exact H|]. intros Hg.
  apply (TR_pre (SPA segs (JAv nd_B2) X_B2 rho2 tp)); [intros w [_ Hw]; exact Hw|].
  apply (CUTS X_B2 nd_B2 0%nat (500, gp (SVar (nB + 3)) 12) rho2 tp); [right; right; right; right; left; reflexivity | exact I |].
  rewrite !efmeas_gp. rewrite (gp_val rho vG 5 _ HF FgB) by lia.
  assert (Eg : uval rho2 (SVar (nB + 3)) = bv_unsigned (rw rho2 (nB + 3)%positive)) by reflexivity.
  pose proof (uval_range rho2 (SVar (nB + 3))) as R.
  rewrite (gp_val' rho2 (SVar (nB + 3)) 12) by lia. lia.
Qed.

Lemma tnz_of_ule4096 : ltac2:(tb__ "0|0|
S15S2S16A1S0S14S14A2S7fS16S17R3A1R2A3S48S4S56S16S1dS1bS1aZ1000A1S9S14S14R2A3A2A1R3A3S5A3S9dR5R3A2F_;F_;Ft;Ffacts;Frho;").
Proof using . intros rho facts t HF C. pose proof (holds_mem _ _ _ HF C) as Hd. apply (proj1 (h_ule _ _ _)) in Hd. rewrite uval_lit in Hd by lia. unfold tnz. change (bv_unsigned (eval rho (fst t))) with (uval rho (fst t)). lia. Qed.

Lemma X_E_fa0 : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S43A2Sb6R3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24Sb6S43A4G1A4S1SeS14Z1c1S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_fa as (_ & _ & _ & _ & _ & _ & _ & _ & Cxf & CdX & CwfE & Cent & Cchk & Cta & Cnp & C12 & C13 & CT0 & Cxb & Ctidy & _).
  pose proof fz_chk_fa as (CR & CX & F4096 & Cpay & Cnb).
  apply (TR_pre (SPA segs (JAv nd_fa) E_fa rho tp)).
  { intros w Hw. rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0)|].
    exact (SPA_axforms segs (JAv nd_fa) xf_fa rho E_fa0 E_fa1 tp w Cxf Hw). }
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (TobjJAKT.free_tol_callT_k segs AE_A AInv CST XGL ALA HCST HXGL HTOP NF Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           E_fa s_fa R_fa rho tp nd_fa 0%nat (pAR, SLit 64) [] _ CFREE
           Cent Cchk Cta Cnp Cnb eq_refl eq_refl).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fa s_fa R_fa rho tvA fr_fz 0%nat (pAR, SLit 64) KU1 ANone eq_refl); [exact CR | exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. exact (tnz_of_ule4096 rho _ (pAR, SLit 64) HFE F4096).
  - intros HP0. exact (proj2 (proj2 HP0)).
  - intros HFc Hagc. exact (Lib_fuzz_one_cov.cov_sound E_fa s_fa R_fa rho0 rho Lib_fuzz_one_cov.cov_fa HFc Hagc).
  - intros rho' tp' _ _. cbn [nd_tv nd_fr nd_am nd_fa tvA remove_nth]. unfold Pre_fr, L_fr in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_e) T_fa rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs _ xfb_fa rho' T_fa0 _ tp' w Cxb Hw). }
    apply (CUTK T_fa nd_e 0%nat (440, z0) rho' tp'); [right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma CXL_sx : ltac2:(tb__ "0|0|
S48S4Sd4VXGL;S8bSe5A1S6S0S14S14A2A1S86S8S3U0A2S6S19A1Sd2Se7A8S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sx_incl : ltac2:(tb__ "0|1|
S10S0S14S14A2M0S55G0R1Se6R2A1A3S55G0R2S12R3A1A3F_;Fr;FE;").
Proof using . intros E r H. unfold X_sx in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma X_sxG : ltac2:(tb__ "0|1|
S10SafS15S2S30Q40A1A1M0SeG0S48S4SabR6Se4R5S37S37A5S5A3S6eS72Z12dS71Z2Z40A2A2R3A2VTR;S32S13VJAv;S37A1R8R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FL;").
Proof.
  intros L s rho tp b tp0 C1 Hb. apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof fz_checks_sx as (_ & _ & _ & _ & _ & _ & Co5 & Cwf5 & CK1 & Cxf & CX2 & Cbase2 & Chf2 & CK3 & Cwf3 & CCepi & CwfC & _).
  pose proof fz_chk_sx as (_ & _ & Cf32 & CRR & CFRF & CX47 & Cbase3 & Cobjs3 & CFx3).
  apply (TR_pre (SPA segs (JAv nd_e) C_epi (rho_sub rho s) tp)).
  { intros w Hw.
    pose proof (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc L K_sx s nd_e nd_e rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw) as Hw1.
    set (r1 := rho_sub rho s) in *.
    assert (Hw2 : SPA segs (JAv nd_e) K_sx2 r1 tp w).
    { apply (SPA_axforms segs _ xf_sx r1 K_sx1 K_sx2 tp w Cxf). rewrite <- CK1.
      apply (SPA_reshape segs _ r1 K_sx 5 _ cfg_mid tp w Co5); [reflexivity | reflexivity | reflexivity | exact Cwf5 | | exact Hw1].
      intros HF. unfold cfg_mid, cfg_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      change (bv_unsigned (eval r1 vCFG)) with (uval r1 vCFG). rewrite (f32_rng r1 _ HF Cf32). unfold uval. lia. }
    assert (Hw3 : SPA segs (JAv nd_e) K_sx3 r1 tp w).
    { rewrite <- CK3. unfold nd_e.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               [] fr_fz [] ANone 0%nat pF 2 pFL gF 0 32 K_sx2 X_sx2 r1 tp w eq_refl ltac:(lia) Cbase2 ltac:(lia)
               ltac:(vm_compute; split; discriminate) Chf2 ltac:(rewrite <- CX2; exact (X_sx_incl K_sx2))
               ltac:(rewrite CK3; exact Cwf3)); [|exact Hw2].
      intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      - exact (fz_robjsR Ai r1 _ [] fr_fz _ rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CRR).
      - intros r y Hr Hy. left. exact (fz_xrsL Ai r1 _ [] fr_fz (Some 0%nat) [] X_sx2 rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CXL_sx r y Hr Hy). }
    rewrite <- CCepi. unfold nd_e.
    apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] fr_fz [] ANone 0%nat pF 2 pFL K_sx3 r1 tp w eq_refl ltac:(lia) Cbase3 ltac:(rewrite CCepi; exact CwfC)); [|exact Hw3].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    - intros o a Ho Hr. rewrite Cobjs3 in Ho. change (ss_facts (ax_S K_sx3)) with (Fx K_sx3) in HF. rewrite CFx3 in HF.
      apply in_app_or in Ho as [Ho|[<-|[]]].
      + destruct (fz_robjsR Ai r1 _ [] fr_fz _ rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CRR o a Ho Hr) as [H|H]; [left; exact H | right; left; exact H].
      + right. right. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf.shobj_range_hse gF pF 256 0 32 r1 _ a ltac:(lia) ltac:(lia) ltac:(vm_compute; split; discriminate) HF CFRF Hr).
    - exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai r1 _ [] _ rho1 tp1 md1 HM HF HN HZ CX47). }
  apply (CUTE C_epi nd_e 0%nat (300, z0) (rho_sub rho s) tp); [right; left; reflexivity | exact I | rewrite efmeas_z0; lia].
Qed.
Lemma X_L_sxK : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S37A2SbbR3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24SbbS37A4G1A4S1SeS14Z1b7S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply TR_JAF. intros _. apply (X_sxG L_sxK s_sxK); [exact (proj1 (proj2 fz_chk_sx)) | rewrite efmeas_z0; lia]. Qed.
Lemma X_L_sxE : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S37A2SbaR3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24SbaS37A4G1A4S1SeS14Z18fS36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply TR_JAF. intros _. apply (X_sxG L_sxE s_sxE); [exact (proj1 fz_chk_sx) | rewrite efmeas_z0; lia]. Qed.

Hypothesis XPOST : ltac2:(tb__ "0|1|
S15S2S30Q40A1A1M0SeG0VTR;S32S13VJAv;Sa5A1ScaR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").

Lemma X_X_rl : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2S37A2Se3R3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24Se3S37A4G1A4S1SeS14Z12bS36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_rl as (Csel & CCrl & CRok & Chf & _).
  pose proof fz_chk_rl as (Cnb & _).
  apply (TR_pre (fun w => exists rho', SPA segs (JAv nd_fz1) C_rl rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X_rl X_rl1 tp _ Csel Hw) as Hw1.
    exists (rho_absorb rho (skipn 7 (ss_objs (ax_S X_rl1))) (vms md tp ms)). rewrite <- CCrl.
    change (ax_setS X_rl1 (set_objs (ax_S X_rl1) (firstn 7 (ss_objs (ax_S X_rl1))))) with (drop_lastA X_rl1 (firstn 7 (ss_objs (ax_S X_rl1)))).
    unfold nd_fz1. change (@nil (sv * Z * sv)) with (remove_nth 0 fr_fz). unfold nd_e in Hw1, Cnb.
    apply (JA_release_inline segs HTOP AInv CST XGL ALA HCST HXGL LFLAG LFSH NF Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] fr_fz [] ANone 0%nat pF 2 pFL gF X_rl1 (firstn 7 (ss_objs (ax_S X_rl1))) (skipn 7 (ss_objs (ax_S X_rl1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact CRok | exact Chf | exact Cnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (CUTE C_rl nd_fz1 0%nat (290, z0) rho' tp); [right; right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|3|
S15S2S30Q40A1A1M0G0VTR;S32S13VJAFv;S4cS35U0M1A2Sa5A2Se2R3R2A5VFAM;S4dS1S0S0S10S24A2M2S3A2S0SeS14A2S1G2S3S1S10S24Se2Sa5A4G1A4S1SeS14Z121S36A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof fz_checks_rl as (_ & _ & _ & _ & _ & _ & Cx1 & Co1 & Cw1 & CHF1 & CHA1 & CU2 & Cx2 & Co3 & Cw3 & CHF3 & CU4 & Cx4 & _).
  pose proof fz_chk_rl as (_ & C1). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_fz1) P_fz (rho_sub rho s_fin) tp)); [|apply XPOST].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_fin P_fz s_fin nd_fz1 nd_fz1 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
  apply (SPA_axforms segs _ [AXSelect [1;0;2;3;4]%nat] rho X_u4 X_fin tp w Cx4). rewrite <- CU4.
  apply (SPA_reshape segs _ rho X_u3 0 _ O_W_fz tp w Co3); [reflexivity | reflexivity | reflexivity | exact Cw3 | |].
  { intros HF. pose proof (has_facts_sound _ _ _ HF CHF3) as HF1. pose proof (al_w rho HF1) as (E1 & E2).
    unfold O_W_fz, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. change fz_frame with 288. rewrite !soff_lit_small by lia. unfold uval in E1, E2. lia. }
  apply (SPA_axforms segs _ xf_un2 rho X_u2 X_u3 tp w Cx2). rewrite <- CU2.
  apply (SPA_reshape segs _ rho X_u1 0 _ oBack tp w Co1); [reflexivity | reflexivity | reflexivity | exact Cw1 | |].
  { intros HF. pose proof (has_facts_sound _ _ _ HF CHF1) as HF1. pose proof (has_facts_sound _ _ _ HF CHA1) as HF2.
    unfold oBack, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    pose proof (al_lo _ HF1 HF2) as E1. pose proof (al_hi _ HF1 HF2) as E2. unfold uval in E1, E2. rewrite soff_lit_small by lia. lia. }
  exact (SPA_axforms segs _ xf_un1 rho X_ret X_u1 tp w Cx1 Hw).
Qed.

Lemma exitsP_ok : ltac2:(tb__ "0|4|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1G1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R7R6A4R5A4R4A4S46A3VTR;S32S13VJAFv;S4cS35R6A2R7A2R8R4R3A5VFAM;S4dS1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsP In] in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-.
  - apply X_L_al.
  - apply X_E_sm0.
  - apply X_X_rel.
  - apply X_E_lo0.
Qed.
Lemma exitsS_ok : ltac2:(tb__ "0|4|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1G1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R7R6A4R5A4R4A4S47A3VTR;S32S13VJAFv;S4cS35R6A2R7A2R8R4R3A5VFAM;S4dS1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <- <- <-.
  - apply X_X_fa0.
  - apply X_X_A.
  - apply X_L_L1.
  - apply X_E_fd0.
  - apply X_X_fa1.
  - apply X_X_B.
  - apply X_L_L3.
Qed.
Lemma exitsK_ok : ltac2:(tb__ "0|4|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1G1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R7R6A4R5A4R4A4S45A3VTR;S32S13VJAFv;S4cS35R6A2R7A2R8R4R3A5VFAM;S4dS1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsK In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply X_E_fa0.
  - apply X_L_sxK.
Qed.
Lemma exitsE_ok : ltac2:(tb__ "0|4|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1M1G1S55S0S0S0S10S24A2M2S3A2M3G0A2S1G3G0S1G2S3S1S10S24R7R6A4R5A4R4A4S44A3VTR;S32S13VJAFv;S4cS35R6A2R7A2R8R4R3A5VFAM;S4dS1G3G0S1G2S3S1S10S24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsE In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  - apply X_L_sxE.
  - apply X_X_rl.
  - apply X_X_ret.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2cS13VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S68S13S62VAInv;VCST;VXGL;A5").
Hypothesis FTC : ltac2:(tb__ "0|0|
Sd8S13S62VAInv;VCST;VXGL;A5").

Hypothesis LOS : ltac2:(tb__ "0|1|
S77OF_;S2S0SeSeA2M0A1S2S0G0SeA2A1S7cS15S2S30Q40A1A1S2cS13VKc;R6A3S7bZ7R4A2S75S13R8S32S13S26VAInv;VCST;VXGL;VKc;S83VCST;R7R6A3R7R6R5S25S84AaSb2R4R3A5S5eS13Sb1R4R3S85VAInv;VCST;VXGL;VKc;R7R6R5A7A5A4F_;F_;Ftp1;Frho1;FBXc;FFFc;FFBc;Fok';").
Variable tp0 : list word.
Let FAMQ : assn := ltac2:(tb__ "0|0|
S5eS13S59Vrho0;Vtp0;ScbVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;A7A5").

Lemma CSM_T : ltac2:(tb__ "0|2|
S5aS15S2S30Q40A1A1S75S13Vok;S32S13S65VAInv;Z2M0R3VKc;A4S88R2R1A5S5eS13S59R2R1S7S0S10S5dA2M1S1S10S5dS87S64VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 2 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CFREE_T : ltac2:(tb__ "0|1|
S5aS15S2S30Q40A1A1S75S13Vok;S32S13Sd7S13VAInv;R3VKc;A4Sb5R2R1A5S5eS13S59R2R1S7S0S10S5dA2M0S1S10S5dSb4S63VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. exact (FTC ok Ai Kc rho1 tp1 HKc (proj1 Hok) (proj2 Hok)). Qed.
Lemma CLO_T : ltac2:(tb__ "0|1|
S2S0SeSeA2M0A1S2S0G0SeA2A1S7cS15S2S30Q40A1A1S7bZ7R3A2S75S13Vok;S32S13S26VAInv;VCST;VXGL;VKc;S83VCST;R6R5A3R6R5R4S25S84AaSb2R3R2A5S5eS13Sb1R3R2Sd3VAInv;VCST;VXGL;VKc;S83VCST;A1S25SaaR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_lo.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (LI.P0_los CST) PTrue LD.Pre_lo LI.nd_lo0 LI.PD_lo LD.NP); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'. exact (LOS ok' FBc' FFc' BXc' rho2 tp2 Hok' HB').
Qed.

Let famS (cuts : list efnode) : Z -> list word -> assn := ltac2:(tb__ "0|0|
SeS2S30Q40A1A1S77S4aSf5S13S80S4fSf3S53VAInv;VCST;VXGL;S59VKc;Vrho0;VP0;VFB;VFF;VBX;S25S35AcS80S4eS4fS51Vcuts;A4A4R1A3VFAMQ;R1A1A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|6|
S2S0S0S0S10S24A2M0S3A2M1S0SeS14A2M2A2M3A1S10S24S3G2S15S2S30Q40A1A1M4SeG4S55G3S1G1G2S1G0S3S1S10S24R8R7A4R6A4R5A4R9A3S4cS35R7R5A3S49S6eZ0S4dS1G1G2S1G0S3S1S10S24RaR9A4R8A4R7A4R6A2M5A2S6fG5R4A2A2S75S13Vok;S32S13VJAv;RaA1RbR7R6A5VfamS;RcR5R4A3A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Fcuts;").
Proof.
  intros cuts T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue PhisZ ok (map efdrop cuts) T nd k FAMQ rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|0|
S2S4eA1S76SeS2S30Q40A1A1S75S13Vok;R3VFAMQ;A4S75S13Vok;R4VfamS;R5R3R2A3A4F_;Ftp0';Fb;FP;Fcuts;").
Proof. intros cuts P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.
Lemma XPOST_T : ltac2:(tb__ "0|0|
S15S2S30Q40A1A1S75S13Vok;S32S13VJAv;Sa5A1ScaR2R1A5VFAMQ;A4Ftp;Frho;").
Proof.
  intros rho tp. eapply triple_conseq; [intros w Hw; exact Hw | | exact (exit_postGA segs AInv CST XGL NF Kc P0 FB FF BX PTrue ok rho0 tp0 nd_fz1 (Posts_fz AInv CST XGL Kc FB FF BX) P_fz (fun _ => False) ltac:(left; reflexivity) rho tp)].
  intros w [[]|Hw]. exact Hw.
Qed.

Lemma E_T : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3bA3S4cS35R5R3A3S75S13Vok;S32S13VJAv;R7A1R8R4R3A5VFAMQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF (map efdrop cutsE) (map efdrop exitsE) ok FAMQ Hok
           (ejcertAF_jcertAF segs NF PhisZ _ _ _ _ _ ecertE_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsE_ok (triple segs ok) (famS cutsE) (TRs_pre segs ok) (@triple_ex segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (reenterS cutsE)
           (fun rho tp b tp0' => rightS cutsE _ b tp0' (XPOST_T rho tp)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma K_T : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3cA3S4cS35R5R3A3S75S13Vok;S32S13VJAv;R7A1R8R4R3A5VFAMQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF (map efdrop cutsK) (map efdrop exitsK) ok FAMQ Hok
           (ejcertAF_jcertAF segs NF PhisZ _ _ _ _ _ ecertK_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsK_ok (triple segs ok) (famS cutsK) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsK _ b tp0' (E_T T nd k rv rho tp Hi Hp))
           CFREE_T (reenterS cutsK) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma S_T : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3eA3S4cS35R5R3A3S75S13Vok;S32S13VJAv;R7A1R8R4R3A5VFAMQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF (map efdrop cutsS) (map efdrop exitsS) ok FAMQ Hok
           (ejcertAF_jcertAF segs NF PhisZ _ _ _ _ _ ecertS_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS_ok (triple segs ok) (famS cutsS) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (reenterS cutsS) CFREE_T
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsS _ b tp0' (K_T T nd k rv rho tp Hi Hp)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma P_T : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3dA3S4cS35R5R3A3S75S13Vok;S32S13VJAv;R7A1R8R4R3A5VFAMQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF (map efdrop cutsP) (map efdrop exitsP) ok FAMQ Hok
           (ejcertAF_jcertAF segs NF PhisZ _ _ _ _ _ ecertP_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsP_ok (triple segs ok) (famS cutsP) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CSM_T (reenterS cutsP) CLO_T
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsP _ b tp0' (S_T T nd k rv rho tp Hi Hp))
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsP _ b tp0' (E_T T nd k rv rho tp Hi Hp)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem fuzz_one_T0 : ltac2:(tb__ "0|0|
S75S13Vok;S32S13S26VAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S25Sa4AaSa7Vrho0;Vtp0;A5VFAMQ;A4").
Proof.
  eapply triple_conseq; [ | intros w Hw; exact Hw | exact (P_T Pre_fz nd_fz0 0%nat (1000, z0) rho0 tp0 ltac:(left; reflexivity) I)].
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S69S13S62VAInv;VCST;VXGL;A5").
Hypothesis FTCX : ltac2:(tb__ "0|0|
Sd9S13S62VAInv;VCST;VXGL;A5").
Hypothesis LOSX : ltac2:(tb__ "0|1|
S2S0SeSeA2M0A1S2S0G0SeA2A1S7cS15S2S30Q40A1A1S7bZ7R3A2S74S13S32S13S26VAInv;VCST;VXGL;VKc;S83VCST;R6R5A3R6R5R4S25S84AaSb2R3R2A5S5eS13Sb1R3R2S85VAInv;VCST;VXGL;VKc;R6R5R4A7A5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Variable tp0 : list word.
Let FAMQ : assn := ltac2:(tb__ "0|0|
S5eS13S59Vrho0;Vtp0;ScbVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;A7A5").
Let FAM : Z -> list word -> assn := fun _ _ w => FAMQ w.

Lemma CSM_E : ltac2:(tb__ "0|2|
S5aS15S2S30Q40A1A1S74S13S32S13S65VAInv;Z2M0R3VKc;A4S88R2R1A5S5eS13S59R2R1S7S0S10S5dA2M1S1S10S5dS87S64VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 2 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma CFREE_E : ltac2:(tb__ "0|1|
S5aS15S2S30Q40A1A1S74S13S32S13Sd7S13VAInv;R3VKc;A4Sb5R2R1A5S5eS13S59R2R1S7S0S10S5dA2M0S1S10S5dSb4S63VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. exact (FTCX Ai Kc rho1 tp1 HKc). Qed.
Lemma CLO_E : ltac2:(tb__ "0|1|
S2S0SeSeA2M0A1S2S0G0SeA2A1S7cS15S2S30Q40A1A1S7bZ7R3A2S74S13S32S13S26VAInv;VCST;VXGL;VKc;S83VCST;R6R5A3R6R5R4S25S84AaSb2R3R2A5S5eS13Sb1R3R2Sd3VAInv;VCST;VXGL;VKc;S83VCST;A1S25SaaR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_lo.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (LI.P0_los CST) PTrue LD.Pre_lo LI.nd_lo0 LI.PD_lo LD.NP); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'. exact (LOSX FBc' FFc' BXc' rho2 tp2 HB').
Qed.

Let famE (cuts : list efnode) : Z -> list word -> assn := ltac2:(tb__ "0|0|
SeS2S30Q40A1A1S77S4aSf4S13S80S4eSf2S52VAInv;VCST;VXGL;S59VKc;Vrho0;VP0;VFB;VFF;VBX;S25S35AcVcuts;A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|6|
S2S0S0S0S10S24A2M0S3A2M1S0SeS14A2M2A2M3A1S10S24S3G2S15S2S30Q40A1A1M4SeG4S55G3S1G1G2S1G0S3S1S10S24R8R7A4R6A4R5A4R9A3S4cS35R7R5A3S49S6eZ0S4dS1G1G2S1G0S3S1S10S24RaR9A4R8A4R7A4R6A2M5A2S6fG5R4A2A2S74S13S32S13VJAv;RaA1RbR7R6A5VfamE;RcR5R4A3A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Fcuts;").
Proof.
  intros cuts T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue PhisZ cuts T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|0|
S2S4eA1S76SeS2S30Q40A1A1S74S13R3VFAMQ;A3S74S13R4VfamE;R5R3R2A3A3F_;Ftp0';Fb;FP;Fcuts;").
Proof. intros cuts P b tp0' H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.
Lemma XPOST_E : ltac2:(tb__ "0|0|
S15S2S30Q40A1A1S74S13S32S13VJAv;Sa5A1ScaR2R1A5VFAMQ;A3Ftp;Frho;").
Proof.
  intros rho tp. eapply etriple_conseq; [intros w Hw; exact Hw | | exact (eexit_postGA segs AInv CST XGL NF Kc P0 FB FF BX PTrue rho0 tp0 nd_fz1 (Posts_fz AInv CST XGL Kc FB FF BX) P_fz (fun _ => False) ltac:(left; reflexivity) rho tp)].
  intros w [[]|Hw]. exact Hw.
Qed.

Lemma E_E : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3bA3S4cS35R5R3A3S74S13S32S13VJAv;R7A1R8R4R3A5VFAM;S4dS1G2G0S1G1S3S1S10S24R8R7A4R6A4R5A4R4A2Vtp0;A2A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF cutsE exitsE (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => Hw) ecertE_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsE_ok (etriple segs) (famE cutsE) (TRe_pre segs) (@etriple_ex segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           (reenterE cutsE)
           (fun rho tp b tp0' => rightE cutsE _ b tp0' (XPOST_E rho tp)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma K_E : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3cA3S4cS35R5R3A3S74S13S32S13VJAv;R7A1R8R4R3A5VFAM;S4dS1G2G0S1G1S3S1S10S24R8R7A4R6A4R5A4R4A2Vtp0;A2A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF cutsK exitsK (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => Hw) ecertK_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsK_ok (etriple segs) (famE cutsK) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightE cutsK _ b tp0' (E_E T nd k rv rho tp Hi Hp))
           CFREE_E (reenterE cutsK) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma S_E : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3eA3S4cS35R5R3A3S74S13S32S13VJAv;R7A1R8R4R3A5VFAM;S4dS1G2G0S1G1S3S1S10S24R8R7A4R6A4R5A4R4A2Vtp0;A2A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF cutsS exitsS (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => Hw) ecertS_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS_ok (etriple segs) (famE cutsS) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           (reenterE cutsS) CFREE_E
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightE cutsS _ b tp0' (K_E T nd k rv rho tp Hi Hp)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma P_E : ltac2:(tb__ "0|3|
S10S24S3S0SeS14A2M0S15S2S30Q40A1A1S55S0S0S0S10S24A2M1S3A2M2G0A2S1G2G0S1G1S3S1S10S24R6R5A4R4A4R3A4S3dA3S4cS35R5R3A3S74S13S32S13VJAv;R7A1R8R4R3A5VFAM;S4dS1G2G0S1G1S3S1S10S24R8R7A4R6A4R5A4R4A2Vtp0;A2A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_fz cps_fz NF cutsP exitsP (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => Hw) ecertP_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsP_ok (etriple segs) (famE cutsP) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CSM_E (reenterE cutsP) CLO_E
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightE cutsP _ b tp0' (S_E T nd k rv rho tp Hi Hp))
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightE cutsP _ b tp0' (E_E T nd k rv rho tp Hi Hp)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem fuzz_one_E0 : ltac2:(tb__ "0|0|
S74S13S32S13S26VAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S25Sa4AaSa7Vrho0;Vtp0;A5VFAMQ;A3").
Proof.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | exact (P_E Pre_fz nd_fz0 0%nat (1000, z0) rho0 tp0 ltac:(left; reflexivity) I)].
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem fuzz_one_T : ltac2:(tb__ "0|4|
S5aS15S2S30Q40A1A1S78OF_;F_;F_;F_;S2S0SeSeA2A1M0G0S6aS13R3R2A3SeSa3R4R1A2S49S6eZ0M1R2A2S6fR2Sc7A2A2F_;Fa;M2G2SeSa6R1A1Sa3R6R2A2F_;Fa;Sd5R7A1Sd6R8A1S66S67R1A1S77OF_;S2cS13R3R1A3S68S13S62RdRcRbA5SeS55SeR1S7SeG1S7SeZf5S7SeZf8S6SeA1A3A3A3A3SedS13S62R10RfReR2A6F_;Fxx;SdbS13S62RfReRdSdaA6SddS13S62R10RfReSdfZcM3A7SddS13S62R11R10RfSe0G3A7Sf0Sd8S13S62R13R12R11A5SceR14R13R12RbR9A5FFTC;FLO;FMCROML;FMCROM;FMC48;FSSC;FAC;FHok;Fok;FHKc;FKc;FLFSH;FLFLAG;FHXlits;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").
Proof.
  intros AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc ok Hok AC SSC MC48 MCROM MCROML LO FTC FB FF BX rho0 tp0 HBX.
  apply (fuzz_one_T0 AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC FTC).
  intros ok' FBc FFc BXc rho1 tp1 Hok' HB'.
  exact (LO AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FBc FFc BXc HB' rho1 ok' Hok' AC SSC MC48 MCROM MCROML tp1).
Qed.

Theorem fuzz_one_E : ltac2:(tb__ "0|4|
S5aS15S2S30Q40A1A1S78OF_;F_;F_;F_;S2S0SeSeA2A1M0G0S6aS13R3R2A3SeSa3R4R1A2S49S6eZ0M1R2A2S6fR2Sc7A2A2F_;Fa;M2G2SeSa6R1A1Sa3R6R2A2F_;Fa;Sd5R7A1Sd6R8A1S66S67R1A1S69S13S62RbRaR9A5SeS55SeR1S7SeG1S7SeZf5S7SeZf8S6SeA1A3A3A3A3SeeS13S62ReRdRcR2A6F_;Fxx;SdcS13S62RdRcRbSdaA6SdeS13S62ReRdRcSdfZcM3A7SdeS13S62RfReRdSe0G3A7Sf1Sd9S13S62R11R10RfA5ScdR12R11R10R9A4FFTCX;FLOX;FMCROMLX;FMCROMX;FMC48X;FSSCX;FACX;FHKc;FKc;FLFSH;FLFLAG;FHXlits;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").
Proof.
  intros AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc ACX SSCX MC48X MCROMX MCROMLX LOX FTCX FB FF BX rho0 tp0 HBX.
  apply (fuzz_one_E0 AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX FTCX).
  intros FBc FFc BXc rho1 tp1 HB'.
  exact (LOX AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FBc FFc BXc HB' rho1 ACX SSCX MC48X MCROMX MCROMLX tp1).
Qed.
