(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "nat"; "true"; "bool"; "cons"; "app"; "fst"; "Some"; "nil"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "sprop"; "holds"; "ss_next"; "SLit"; "SPUle"; "rw"; "sprop_eqb"; "SVar"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "TPA"; "fbinA"; "ffinA"; "frinA"; "tvinA"; "AHead"; "JA"; "NDA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tblB"; "V_B"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago_pf.FSP"; "P0_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago_pf.IRP"; "P0_ir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "keptK"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_ir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago"; "kept_fs"; "kept_go"; "PDk_fs"; "PDk_go"; "E_fs"; "R_fs"; "R_go"; "E_fs0"; "E_fs1"; "E_go"; "T_fs_fz"; "T_fs_nop"; "T_fs_ok"; "Xk_fs"; "Xk_go"; "brest_go"; "nd_go_ok"; "nnPhi"; "passed_fs"; "passed_go"; "qH1"; "s_fs"; "s_go"; "tv_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago_eqs"; "cutsG"; "nd_fzX"; "nd_nopX"; "nd_okX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago_pf.FS"; "NP"; "Pre_fs"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago_pf.IR"; "Pre_ir"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "HNEXT"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopEf"; "ndXEf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_finalize_shape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_loopEf Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_ago Lib_load_obj_ago_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module IR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest. End IR.  Module IRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_intern_rest_pf. End IRP.
Module FS. Include Lib_finalize_shape. End FS.  Module FSP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf. End FSP.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S3bS2S1SfA1M0S10OF_;M1A2M2G2S49S9G0G1R1A3SdG0G1R1A3A2Lp;S76A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma V_B_agree_ge : ltac2:(tb__ "0|0|
SfS10S10S34S6S9aS84R3A2S5A3S4dR4R3R2A3SfS39SfR1S38A3S34S1fQ40A1S18R5R2A2S18R6R2A2A3F_;Fv;F_;F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Hn [HV HL]. apply V_B_agree. split; [|exact HL].
  intros i Hi. apply HV. apply Pos.leb_le in Hn. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S8aS10S1S1fQ40A1A1S3dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S99S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SeS8dVCST;R1A2S33S55Z0R2A2S56R2S95A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SeS8dVXGL;R1A2S33S55Z0R2A2S56R2S95A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SeS9cR1A1S8dVXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1S2S2SeSeA2SeA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S10OFr;") := ltac2:(tb__ "0|0|
S9eVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S29VAInv;VCST;VXGL;S77VKc;Vrho0;VP0;VFB;VFF;VBX;S21Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S48VAInv;VCST;VXGL;S77VKc;Vrho0;VP0;VFB;VFF;VBX;S21VPhi;Vnd;Ad").

Lemma HIN_go : ltac2:(tb__ "0|1|
S10S57S8aS10S1S1fQ40A1A1S3dS3bS13S14R6A1S12S1dS67A1A1A3VP0;Vrho0;A1S4dS77Vrho0;R8A3VAInv;R7R6R5R4A4S23Vrho0;R8A2S8fRbS8cS8bR9A1A1A2S24VFB;RaA2S25VFF;RbA2S27VFB;RcReS8S2S11S11A2S5fS71A3M0A4S90RfG0A2S91R10G0A2S26VFF;RfR11S36A4S33S93VCST;Vrho0;VFB;VFF;R12S5fS36S64A8S33S94VCST;VXGL;Vrho0;VFB;VFF;R12S5fS36S6cA9S40VCST;S8eVFB;R12S5fA3S92VFF;R12S36A3S4bS4aR12S64R11A3S74A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof ago_checks3 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_go) by (apply (tvinA_sublist FB Ai rho (kept_go ++ passed_go)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_go) by (exact (tvd_app_l rho kept_go passed_go HD)).
  assert (HZk : tvz rho kept_go) by (apply (tvz_sublist rho (kept_go ++ passed_go)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_go frL extra_go R_go rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_go in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_go frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_go frL o a HF CLN HT0 HZk lines_in_kept_go HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_go frL xextraLO Xk_go rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_go frL r a Hav HP0 HE Ha).
  - pose proof ago_checks1 as (_ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold IRP.P0_ir, uval, Lib_scan_double.vB, Lib_scan_double.vL, IR.vBld. cbn [eval]. rewrite !rw_call'.
    change (wsub_get s_go 15) with vBUF. change (wsub_get s_go 18) with vLEN. change (wsub_get s_go 12) with bA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split.
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_go rho R_go ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho kept_go) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_go) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
Qed.

Lemma HIN_fs : ltac2:(tb__ "0|1|
S10S57S8aS10S1S1fQ40A1A1S3dS3bS13S14R6A1S12S1dS62A1A1A3VP0;Vrho0;A1S4dS77Vrho0;R8A3VAInv;R7R6R5R4A4S23Vrho0;R8A2S8fRbS8cS8bR9A1A1A2S24VFB;RaA2S25VFF;RbA2S27VFB;RcReS8S2S11S11A2S5eS70A3M0A4S90RfG0A2S91R10G0A2S26VFF;RfR11S36A4S33S93VCST;Vrho0;VFB;VFF;R12S5eS36S63A8S33S94VCST;VXGL;Vrho0;VFB;VFF;R12S5eS36S6bA9S3fS8eVFB;R12S5eA3S92VFF;R12S36A3S4bS4aR12S63R11A3S73A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof ago_checks3 as (_ & _ & _ & CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_fs) by (apply (tvinA_sublist FB Ai rho (kept_fs ++ passed_fs)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_fs) by (exact (tvd_app_l rho kept_fs passed_fs HD)).
  assert (HZk : tvz rho kept_fs) by (apply (tvz_sublist rho (kept_fs ++ passed_fs)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_fs frL extra_go R_fs rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_go in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_fs frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_fs frL o a HF CLN HT0 HZk lines_in_kept_fs HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_fs frL xextraLO Xk_fs rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_fs frL r a Hav HP0 HE Ha).
  - unfold FSP.P0_fs. rewrite !rw_call'.
    change (wsub_get s_fs 12) with bA. change (wsub_get s_fs 100) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
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
SeS1S1fQ40A1A1S2fF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2dS1cS10S1S1fQ40A1A1S2fS3bS13S14R3A1S12S1dR4A1A1A3VTR;S2cS0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2fS2fS2fS32R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2fOS2fS32R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2dS2dS1cS1cS4cS1S1bA1M0S1S2S1cS42A2M1A1S1S2S11S11A2M2A1S2fS10S1S1fQ40A1A1M3G2S39G2R1R5A3S39G2R2S1eRbA1A3F_;Fr;S34ScG0A1S45RaR9R8A3SaG0R7A2A3S34S6S44RbRaR9R8S3cG1S1cS9S1cS42A2R7A4A5S5A3S10G3VTR;S2cS0RfRdR2R1A5S41S0S15S1dRdA1A1R2R1RaA5A2Ftp1;Frho1;S1S3eA1M4S57S3dS2eS0R9R8R10S3G4S78R3S79R2R1A2A4A5R13RaR9R4R2A4R13S4bS4aRbRfS4fR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S1cS42G4S57S3dS10G3G4S57S3dS39G1S3S1cS42RaR9A4R14A3S2eS0R12R11R19S3G4S78R9S79R8R7A2A4A5R1cR13R12RaR8A4S4dS15S1dR1aA1A1S4bS4aR14R18S4fR9R13RaA3A3R19A2R8A3S2eS0R9R8ReS3G4S78R7S79R6R5A2A4A5ReS4bS4aR16R1aS4fRbR15RcA3A3R1bA2R15RaR9R8R6A6S33S9fR17S4fRcR16RdA3R1bR1cR1dR10R1eR19RbA9S10S4eR18S4fRdR17ReA3R1cR1dS1dR1eA1S1dR1fA1S1dR11A1R1RcA9VTR;S2cS0S43R11S4bS4aR19R1dS4fReR18RfA3A3R1eA2R18RdRcA5Sa0R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2cS0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S10OF_;S20S1cS10S1S1fQ40A1A1S2fR6R3A1VTR;S2cS0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S2cS0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHI : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S51S10S1S1fQ40A1A1S50Z5R3A2VTR;S2cS0S22VAInv;VCST;VXGL;VKc;S40VCST;R6R5A3R6R5R4S21S82AaS81R3R2A5S41S0S89R3R2S53VAInv;VCST;VXGL;VKc;S40VCST;A1S21S61R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CHF : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S51S10S1S1fQ40A1A1S50Z5R3A2VTR;S2cS0S22VAInv;VCST;VXGL;VKc;S3fR6R5A2R6R5R4S21S80AaS7fR3R2A5S41S0S7eR3R2S53VAInv;VCST;VXGL;VKc;S3fS21S60R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Lemma tblB_call : ltac2:(tb__ "0|3|
S1cS1S2S11S11A2M0A1SfS10S10S3bS13S14R2A1S12S1dR5A1A1A3S34S6S9dS12S1dR6A1A1A1S5A3S34S6S3aS13S19S17S1aP1eA1M1S16Z7fffff800000A1A2A1S12S1dR7A1A1A3S5A3S34S6S3aS13S19S17S16Z7fff7f800000A1G1A2A1S12S1dR8A1A1A3S5A3S34S6S9aS84R7A2S5A3S4dR8R7R6A3S54VCST;Vrho0;VFB;VFF;R8RaS36R7A8S39G0S3S11S11S85S9bZ10S86A2A4RbA3S35S34SeS52RaS85A2Z0A3A1S37RbA1M2G2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho';Frho;Fn;Fkept;FA;").
Proof.
  intros A kept n rho rho' HF CLN C30 C30a Hn Hag HK Hin Hdnz HPHI.
  pose proof (holds_mem _ _ _ HF C30) as HtB. rewrite h_ule, uval_lit in HtB by lia.
  pose proof (holds_mem _ _ _ HF C30a) as HtA. rewrite h_ule, uval_lit in HtA by lia.
  destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
  apply (tblB_kept rho rho' (V_B_agree_ge n rho rho' Hn Hag)); [| exact HiC | exact HcK | exact HPHI].
  apply (keptK_lines CST FB FF rho0 rho kept frL rho' HK Hin Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia].
Qed.

Lemma nnPhi_holds : ltac2:(tb__ "0|0|
S10S1S1fQ40A1A1S1S3eA1S3dS3bS13S14R4A1S12S1dS66A1A1A3VJAv;S2aS75S36S6dS28S72S5A2A4R5R4R3R2A5S14R6S6fA2F_;F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md HF (Ai & kc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBU & _).
  cbn [nd_bd] in HBU. destruct HBU as (_ & _ & _ & _ & _ & _ & Hnn & _).
  assert (Hin : In (nth 14 brest_go (BIc 0 0 0)) brest_go) by (apply (nth_error_In _ 14); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (Forall_forall _ _) Hnn _ Hin) as N0.
  change (nth 14 brest_go (BIc 0 0 0)) with (PHIe 128 (t_c (v_sh vsP)) (t_k (v_sh vsP))) in N0.
  unfold PHIe in N0. cbv beta iota delta [bival lfval aval bi_f bi_c] in N0.
  fact HF (SPUle (kb 128 (t_k (v_sh vsP))) (SLit 4294967295)) F1. fact HF (SPUle (t_c (v_sh vsP)) (t_k (v_sh vsP))) F2. fact HF (SPUle (t_k (v_sh vsP)) (SLit 4294967295)) F3.
  rewrite h_ule in F1, F2, F3. rewrite uval_lit in F1, F3 by lia.
  pose proof (uval_range rho (t_c (v_sh vsP))) as Rc. pose proof (uval_range rho (kb 128 (t_k (v_sh vsP)))) as Rk.
  assert (Ec : uval rho (kb 128 (t_c (v_sh vsP))) = 128 * uval rho (t_c (v_sh vsP))) by (unfold kb; apply uval_mul_lit; lia).
  rewrite uval_lit in N0 by lia.
  unfold nnPhi. rewrite h_ule.
  rewrite (uval_mul_lit rho 4 (kb 128 (t_k (v_sh vsP)))) by lia.
  rewrite uval_add_small; rewrite ?uval_lit by lia; rewrite ?(uval_mul_lit rho 6 (kb 128 (t_c (v_sh vsP)))) by lia; lia.
Qed.

Lemma site_fs : ltac2:(tb__ "0|4|
S10S1S1fQ40A1A1M0S2fS37R3A1M1S1cS20S10G0S39S2S1cS20A2M2S3S1cS20R4R3A4S7G2S3S1cS20S69S7cA4S7G2S3S1cS20S6aS7dA4S7G2S3S1cS20S68S7bA4SbG2A1A3A3A3A3G1S3bS13S14RaA1S12S1dS62A1M3A1A3S4dS15G3A1RbR5A3VTR;S2cS0VJAv;R7A1R8R6R5A5RaA2F_;F_;F_;F_;Ftp';Frho';Fnd;FT;VTR;S2cS0VJAv;S6eA1S65R5R4A5R3A2F_;F_;FQ;Ftp;Frho;").
Proof.
  intros rho tp Q HPHI HKont.
  pose proof ago_checks2 as (_ & _ & Cxf & Cfeq & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnh).
  pose proof ago_checks3 as (_ & _ & _ & _ & _ & CLN & _).
  set (ndv := NDA tv_fs frL brest_go (AHead qH1 true)).
  apply (TR_pre (SPA segs (JAv ndv) E_fs rho tp)).
  { intros w Hw. rewrite <- Cfeq. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_fs rho E_fs0 E_fs1 tp w Cxf).
      unfold ndv, tv_fs. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL brest_go _ E_fs0 rho tp w Cptv Hw).
    -
      intros tr md HJ HF1. apply Forall_app. split; [|exact HF1]. constructor; [|constructor].
      exact (nnPhi_holds rho tp tr md HF1 HJ). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_fs HF CLN HTK HZ). unfold tv_fs. apply in_or_app. left. exact lines_in_kept_fs. }
  intros Hdnz.
  unfold ndv, tv_fs.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX FSP.P0_fs PTrue (fun _ H => H) (fun _ _ _ H => H)
           FS.Pre_fs FS.nd0 PDk_fs FS.NP eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHF eq_refl
           E_fs s_fs R_fs Xk_fs rho tp kept_fs passed_fs frL brest_go brest_fs (AHead qH1 true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - unfold payA. apply (pay_okF_split _ _ _ _ brest_go _ bdrest_fs payX_fs payY_fs PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_fs rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : tblB rho').
    { apply (tblB_call E_fs kept_fs _ rho rho' HF CLN ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Cnh Hag HK lines_in_kept_fs Hdnz HPHI). }
    pose proof ago_checks2_nd as (Cndn & Cndo & Cndz & CTn & CTo & CTf & CTz & Bn & Bo & Bz & Tin & Tio & Tiz & Pn & Po & Pz & CABS & _).
    cbn [PDk_fs liftPD FSP.PD_fs map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[Hd|[]]]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTn, Cndn.
      apply (TR_pre (SPA segs (JAv nd_fs_nop) T_fs_nop rho' tp')).
      { intros w Hw. rewrite <- Tin. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fs_nop) (xfb_fs T_fs_nop0) rho' T_fs_nop0 B_fs_nop tp' w Bn Hw). }
      apply TR_facts. intros HFn. pose proof ago_checks_pay2 as (Q1 & Q2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_nopX) T_fs_nop rho' tp')).
      { intros w Hw. unfold nd_nopX.
        apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_nop tvL frL bdX_nop (AHead qHn true) T_fs_nop rho' tp' w Pn).
        unfold nd_fs_nop in Hw.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_nop frL (AHead qHn true) bd_fs_nop comm_nop Xs_nop Ys_nop bdX_nop _ T_fs_nop rho' tp' w Q1 Q2 HFn QPay Hw). }
      apply (HKont T_fs_nop nd_nopX rho' tp'); [left; reflexivity | exact HPHI' | exact HF | exact Hag].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_fs_ok) T_fs_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fs_ok) (xfb_fs T_fs_ok0) rho' T_fs_ok0 B_fs_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof ago_checks_pay2 as (_ & _ & _ & _ & Q1 & Q2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_okX) T_fs_ok rho' tp')).
      { intros w Hw. unfold nd_okX.
        apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_ok tvL_ok frL bdX_ok (AHead qHk true) T_fs_ok rho' tp' w Po).
        unfold nd_fs_ok in Hw.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_ok frL (AHead qHk true) bd_fs_ok comm_ok Xs_ok Ys_ok bdX_ok _ T_fs_ok rho' tp' w Q1 Q2 HFo QPay Hw). }
      apply (HKont T_fs_ok nd_okX rho' tp'); [right; left; reflexivity | exact HPHI' | exact HF | exact Hag].
    +
      rewrite CTf. apply TR_facts. intros HFf. exfalso.
      pose proof (holds_mem _ _ _ HFf CABS) as FA. cbn [holds f_absurd] in FA. apply FA. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    +
      rewrite CTz, Cndz.
      apply (TR_pre (SPA segs (JAv nd_fs_fz) T_fs_fz rho' tp')).
      { intros w Hw. rewrite <- Tiz. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fs_fz) (xfb_fs T_fs_fz0) rho' T_fs_fz0 B_fs_fz tp' w Bz Hw). }
      apply TR_facts. intros HFz. pose proof ago_checks_payf2 as (Q1 & Q2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_fzX) T_fs_fz rho' tp')).
      { intros w Hw. unfold nd_fzX.
        apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_fz tvL frL bd_fzX (AHead qHz false) T_fs_fz rho' tp' w Pz).
        unfold nd_fs_fz in Hw.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_fz frL (AHead qHz false) bd_fs_fz commf_fz Xf_fz Yf_go bd_fzX _ T_fs_fz rho' tp' w Q1 Q2 HFz QPay Hw). }
      apply (HKont T_fs_fz nd_fzX rho' tp'); [right; right; left; reflexivity | exact HPHI' | exact HF | exact Hag].
Qed.

Hypothesis CUTV : ltac2:(tb__ "0|5|
S1cS20S4S2SeS11A2M0S10S1S1fQ40A1A1M1SeG1S39S2S2S2S1cS20A2M2S4A2M3G0A2S3G3G0S3G2S4S3S1cS20R8R7A4R6A4R5A4S7aA3S47S76R7R5A3S33S55Z0S46S3G3G0S3G2S4S3S1cS20RaR9A4R8A4R7A4R6A2M4A2S56G4R4A2A2VTR;S2cS0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_go : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0VTR;S2cS0VJAFv;S37S58A2S5dR3R2A5VFAM;S46S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S5dS58A4U1A4S3SeS11S59S5aZ11S5bA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof ago_checks1 as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Ctv & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnx).
  pose proof ago_checks3 as (_ & _ & CLN & _).
  set (ndv := NDA tv_go frL (bdA A1) (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_go rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) xf_go rho E_ir E_go tp w Cxf). unfold ndv. rewrite Ctv. exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_go HF CLN HTK HZ). unfold tv_go. apply in_or_app. left. exact lines_in_kept_go. }
  intros Hdnz.
  unfold ndv, tv_go.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (IRP.P0_ir CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           IR.Pre_ir IR.nd0 PDk_go NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHI eq_refl
           E_go s_go R_go Xk_go rho tp kept_go passed_go frL (bdA A1) brest_go (AHead pH true) (FAM (efmeasA (E_ir, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - unfold payA. apply (pay_okF_split _ _ _ _ (bdA A1) _ bd_rest payX_go payY_go PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_go rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : tblB rho').
    { apply (tblB_call E_go kept_go (ss_next (ax_S E_go)) rho rho' HF CLN ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(rewrite Cnx; reflexivity) Hag HK lines_in_kept_go Hdnz HPHI). }
    rewrite Cnx in Hag.
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof ago_checks1_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & _).
    cbn [PDk_go liftPD IRP.PD_ir map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_go_f) T_go_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_go_f) (xfb_go T_go_f0) rho' T_go_f0 B_go_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof ago_checks_payf1 as (QP1 & QP2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_go_fX) T_go_f rho' tp')).
      { intros w Hw. unfold nd_go_fX, nd_go_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_go_f frL (AHead pH false) bd_go_f commf_go Xf_go Yf_go bd_go_fX _ T_go_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_go_f nd_go_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_ir T_go_f ndA1 nd_go_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_go_ok) T_go_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_go_ok) (xfb_go T_go_ok0) rho' T_go_ok0 B_go_ok tp' w Bo Hw). }
      apply (CUTV T_go_ok nd_go_ok 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_ir T_go_ok ndA1 nd_go_ok 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2bS0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S97S0S96VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S10S1S1fQ40A1A1M0G0S31S0Vok;S2cS0VJAFv;S37S5cA2S83R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2f : ltac2:(tb__ "0|1|
S10S1S1fQ40A1A1M0G0S31S0Vok;S2cS0VJAFv;S37S88A2S87R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHI_T : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S51S10S1S1fQ40A1A1S50Z5R3A2S31S0Vok;S2cS0S22VAInv;VCST;VXGL;VKc;S40VCST;R6R5A3R6R5R4S21S82AaS81R3R2A5S41S0S89R3R2S53VAInv;VCST;VXGL;VKc;S40VCST;A1S21S61R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_go.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (IRP.P0_ir CST) PTrue IR.Pre_ir IR.nd0 IRP.PD_ir NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (IRP.intern_rest_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.
Lemma CHF_T : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S51S10S1S1fQ40A1A1S50Z5R3A2S31S0Vok;S2cS0S22VAInv;VCST;VXGL;VKc;S3fR6R5A2R6R5R4S21S80AaS7fR3R2A5S41S0S7eR3R2S53VAInv;VCST;VXGL;VKc;S3fS21S60R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs.
  eapply (sum_PostsC_k segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (FSP.finalize_shape_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S1cS20S4S2SeS11A2M0S10S1S1fQ40A1A1M1SeG1S39S2S2S2S1cS20A2M2S4A2M3G0A2S3G3G0S3G2S4S3S1cS20R8R7A4R6A4R5A4S7aA3S47S76R7R5A3S33S55Z0S46S3G3G0S3G2S4S3S1cS20RaR9A4R8A4R7A4R6A2M4A2S56G4R4A2A2S31S0Vok;S2cS0VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsG) (map efdrop exitsG) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertG_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsG In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_fs (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CHF_T rho1 tp1 _ HP1).
    intros T' nd'' rho' tp' HinT HP' _ _.
    apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsG) T' nd'' 1%nat (FAMQ tp0') rho' tp'); [| exact HP'].
    cbn [In] in HinT. destruct HinT as [E|[E|[E|[]]]]; injection E as <- <-; cbn [map efdrop cutsG fst snd In]; tauto.
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2f rho1 tp1 tp0')].
Qed.

Theorem arm_go_T : ltac2:(tb__ "0|1|
S10S1S1fQ40A1A1M0G0S31S0Vok;S2cS0VJAFv;S37S58A2S5dR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_go (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHI_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S98S0S96VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
SeS1S1fQ40A1A1S2fF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SeSeS1S1fQ40A1A1S32S55R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0S30S0S2cS0VJAFv;S37S5cA2S83R3R2A5VFAM;S46S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S83S5cA4U1A4S3SeS11S59S5aZ1S5bA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2f : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0S30S0S2cS0VJAFv;S37S88A2S87R3R2A5VFAM;S46S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S87S88A4U1A4S3SeS11S59S5aZ1S5bA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHI_E : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S51S10S1S1fQ40A1A1S50Z5R3A2S30S0S2cS0S22VAInv;VCST;VXGL;VKc;S40VCST;R6R5A3R6R5R4S21S82AaS81R3R2A5S41S0S89R3R2S53VAInv;VCST;VXGL;VKc;S40VCST;A1S21S61R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_go.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (IRP.P0_ir CST) PTrue IR.Pre_ir IR.nd0 IRP.PD_ir NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (IRP.intern_rest_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.
Lemma CHF_E : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S51S10S1S1fQ40A1A1S50Z5R3A2S30S0S2cS0S22VAInv;VCST;VXGL;VKc;S3fR6R5A2R6R5R4S21S80AaS7fR3R2A5S41S0S7eR3R2S53VAInv;VCST;VXGL;VKc;S3fS21S60R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (FSP.finalize_shape_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S1cS20S4S2SeS11A2M0S10S1S1fQ40A1A1M1SeG1S39S2S2S2S1cS20A2M2S4A2M3G0A2S3G3G0S3G2S4S3S1cS20R8R7A4R6A4R5A4S7aA3S47S76R7R5A3S33S55Z0S46S3G3G0S3G2S4S3S1cS20RaR9A4R8A4R7A4R6A2M4A2S56G4R4A2A2S30S0S2cS0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsG exitsG (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertG_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsG In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_fs (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs) CHF_E rho1 tp1 _ HP1).
    intros T' nd'' rho' tp' HinT HP' HF Hag.
    pose proof ago_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cnh).
    assert (E460 : rw rho' 460%positive = rw rho1 460%positive) by (symmetry; apply (proj1 Hag); apply Pos.leb_le in Cnh; unfold HNEXT in Cnh; lia).
    assert (E467 : rw rho' 467%positive = rw rho1 467%positive) by (symmetry; apply (proj1 Hag); apply Pos.leb_le in Cnh; unfold HNEXT in Cnh; lia).
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
    fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    cbn [In] in HinT. destruct HinT as [E|[E|[E|[]]]]; injection E as <- <-.
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsG T_fs_nop nd_nopX 1%nat (RL, VLA 5 z0));
        [right; right; left; reflexivity | exact HP' |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_fs0 T_fs_nop nd_go_ok nd_nopX 1%nat 1%nat); [exact E460 | exact E467 | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsG T_fs_ok nd_okX 1%nat (RL, VLA 5 z0));
        [right; right; right; left; reflexivity | exact HP' |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_fs0 T_fs_ok nd_go_ok nd_okX 1%nat 1%nat); [exact E460 | exact E467 | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsG T_fs_fz nd_fzX 1%nat (RL, VLA 5 z0));
        [right; right; right; right; left; reflexivity | exact HP' |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_fs0 T_fs_fz nd_go_ok nd_fzX 1%nat 1%nat); [exact E460 | exact E467 | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2f rho1 tp1 tp0')].
Qed.

Theorem arm_go_E : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0S30S0S2cS0VJAFv;S37S58A2S5dR3R2A5VFAM;S46S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S5dS58A4U1A4S3SeS11S59S5aZ11S5bA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_go (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHI_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.

