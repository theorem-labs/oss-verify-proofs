(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "SPUle"; "SLit"; "rw"; "holds"; "sprop_eqb"; "sobj"; "ss_next"; "DUnknown"; "SAlu"; "SPEq"; "SVar"; "ss_objs"; "ob_cells"; "swf"; "@Corelib.Init.Datatypes"; "list"; "true"; "bool"; "prod"; "pair"; "cons"; "andb"; "nil"; "app"; "Some"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tblB"; "V_B"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "g5"; "NP"; "vF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "kept_vr"; "cnt_av"; "k_av"; "E_vr1"; "R_vr"; "d_av"; "tv_fail"; "E_vr"; "PD_vr"; "PDk_vr"; "T_fail"; "T_failr"; "T_grown"; "T_grownS"; "T_keep"; "T_keepS"; "Xk_vr"; "c_av"; "cb_av"; "h0"; "nd_fail"; "nd_grown"; "nd_keep"; "objs_nl"; "passed_vr"; "room_av"; "s_vr"; "sh_of"; "slot_facts"; "tv_keep"; "tv_vr"; "vKg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf3"; "slot_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "xLK"; "pH"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "PTrue"; "AHead"; "ndesc"; "ANone"; "JA"; "JA_pre"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "nd_below"; "tvinA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "sub"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "extra_hv"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "X_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3.VR"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3m"; "cp_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf3.Sum.X"; "rel_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf3.Sum"; "reo_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hvpk Lib_load_obj_hv2 Lib_load_obj_hv_pf1 Lib_load_obj_hv3 Lib_load_obj_hv3m.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Lemma h0_ltNF : (h0 < NF)%positive. Proof. reflexivity. Qed.
Lemma HamC_vr : nd_am VR.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vr : ltac2:(tb__ "0|1|
S38S17S24S77A2M0G0S0S7cS80S20S24S77R1A3A1S78A3Ld;S49A3"). Proof. repeat constructor. Qed.
Lemma P0_vr_mono : ltac2:(tb__ "0|2|
S14S17S22S22A2M0A1M1G1S14S17G0S22A2A1S3G0S2dG0R1R5A3S2dG0R2R5A3F_;Fbn;S61R5R3R2A3S61R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.
Lemma lines_in_kept_vr : ltac2:(tb__ "0|0|
S2dS17S2S2A2S18S2S2S67S37Z10S68A2A4S41A3").
Proof. cbn. do 17 right. left. reflexivity. Qed.
Lemma av_in_tv_keep : ltac2:(tb__ "0|0|
S2dS17S2S2A2S18S2S2S46S37Z4S43A2A4S5eA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_tv_fail : ltac2:(tb__ "0|0|
S2dS17S2S2A2S18S2S2S67S37Z10S68A2A4S47A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma av_in_tv_vr : ltac2:(tb__ "0|0|
S2dS17S2S2A2S18S2S2S46S37Z4S43A2A4S5fA3").
Proof. unfold tv_vr. apply in_or_app. right. left. reflexivity. Qed.

Lemma hv3_facts_room : ltac2:(tb__ "0|1|
S1S0S16S2eS4SaS6S52S6aA2A1S5S25S44A1A1M0A3S15A3S1S0S16S2eS4SaS6S6aSeS8eS3dS7Z1A1A3A2A1G0A3S15A3S0S16S2eS4SaS6S3dS7Z4000000A1A2A1G0A3S15A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma room_av_holds : ltac2:(tb__ "0|0|
S3S38S4S9R1A1S5S25S44A1A1A3S9R2S5aA2F_;Frho;").
Proof.
  intros rho HF. pose proof hv3_facts_room as (CC & CN & CL).
  pose proof (holds_mem _ _ _ HF CL) as FL. pose proof (holds_mem _ _ _ HF CC) as FC. pose proof (holds_mem _ _ _ HF CN) as FN.
  rewrite h_ule in FL, FC, FN. rewrite uval_lit in FL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho c_av) as RC.
  rewrite uval_add_small in FN by (rewrite uval_lit by lia; lia). rewrite uval_lit in FN by lia.
  assert (E0 : uval rho cnt_av = 3 * uval rho c_av) by (unfold cnt_av; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  assert (E1 : uval rho (SAlu ALU_ADD cnt_av (SLit 3)) = 3 * uval rho c_av + 3) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (E2 : uval rho (SMd M_MUL (SLit 4) (SAlu ALU_ADD cnt_av (SLit 3))) = 4 * (3 * uval rho c_av + 3)) by (rewrite uval_mul_lit by (rewrite ?E1; lia); rewrite E1; reflexivity).
  unfold room_av. rewrite h_ule, E2. rewrite uval_lit by (unfold VR.B_EW; lia).
  apply (room4_arith (3 * uval rho c_av) (uval rho pNX) (uval rho vLEN) 3); lia.
Qed.

Definition slot_src (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S1aS1aS1aS2eS4SaS6SeS8eS42S7Z3A1A3Vk;A2A1VF;A3S2eS4SaS6S42Vk;A2A1VF;A3A2S2eS4SaS6Vk;S7ZffffffffA1M0A2A1VF;A3A2S2eS4SaS6S37Z4Vk;A2G0A2A1VF;A3A2").
Lemma hv3_facts_slot : ltac2:(tb__ "0|0|
S1S0S16S66S43S5S25S4fA1A1A2S15A3S0S16S66S60S5S25S4dA1A1A2S15A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma slot_vals : ltac2:(tb__ "0|4|
S3S14S4A1S2S38S4S9R3A1R2A3S0S16S66R2R3A2S15A3S1S83S88S70R5S42A2M0Z3A2S70R5R3A2M1A2S1S83S85Z4M2G1A2M3ZffffffffA2S1S0S22S70R5S37G2R3A2A2G3A3S0S22S70R5S53A2S85G2G0A2A3A2A2A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H. unfold slot_src in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  rewrite h_ule in F1, F2, F3, F4. rewrite uval_lit in F3, F4 by lia.
  pose proof (uval_range rho cnt_av) as RC. pose proof (uval_range rho k) as RK.
  rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  assert (E4k : uval rho (kb 4 k) = 4 * uval rho k) by (unfold kb; apply uval_mul_lit; lia).
  assert (E4c : uval rho cb_av = 4 * uval rho cnt_av) by (unfold cb_av; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  rewrite E4k in F4. repeat split; lia.
Qed.
Lemma slot_holds : ltac2:(tb__ "0|0|
S3S14S4A1S2S38S4S9R3A1R2A3S0S16S66R2R3A2S15A3S38S4S9R5A1S5dR3A1A3F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H. destruct (slot_vals rho F k HF H) as (V1 & V2 & V3 & V4).
  pose proof (uval_range rho cnt_av) as RC.
  unfold slot_facts. constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - lia.
  - unfold VR.B32. rewrite uval_lit by lia. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S96S3S14S36Q40A1A1S3fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sb3S21VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S22S8dVCST;R1A2S1S83Z0R2A2S84R2S94A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S22S8dVXGL;R1A2S1S83Z0R2A2S84R2S94A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S22S99R1A1S8dVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S14S17S17S22S22A2S22A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
Sa1VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S79VAInv;VCST;VXGL;S3bVKc;Vrho0;VP0;VFB;VFF;VBX;S75Vnd;Ac").

Lemma HIN_vr : ltac2:(tb__ "0|1|
S3S65S96S3S14S36Q40A1A1S3fS38S4S9R6A1S5S25S48A1A1A3VP0;Vrho0;A1S92S3bVrho0;R8A3VAInv;R7R6R5R4A4S7bVrho0;R8A2Sa4RbS98S97R9A1A1A2S7dVFB;RaA2S7eVFF;RbA2S82VFB;RcReS1cS17S2S2A2S41S59A3M0A4Sa5RfG0A2Sa6R10G0A2S7fVFF;RfR11S30A4S1SaaVCST;Vrho0;VFB;VFF;R12S41S30S45A8S1SacVCST;VXGL;Vrho0;VFB;VFF;R12S41S30S51A9S61Sa3VFB;R12S41A3Sa9VFF;R12S30A3S63S62R12S45R11A3S5bA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof hv3_checks_vr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN & _).
  assert (HNk : tvinA FB Ai rho kept_vr) by (apply (tvinA_sublist FB Ai rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vr) by (exact (tvd_app_l rho kept_vr passed_vr HD)).
  assert (HZk : tvz rho kept_vr) by (apply (tvz_sublist rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF AInv CST ALA HCST FB FF rho0 Ai rho _ kept_vr R_vr rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CLN lines_in_kept_vr CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_vr Xk_vr rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold P0_vr. rewrite !rw_call'.
    change (wsub_get s_vr 17) with k_av. change (wsub_get s_vr 15) with d_av. change (wsub_get s_vr 12) with (SAlu ALU_ADD vF (SLit 568)). change (wsub_get s_vr 14) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E664 : uval rho (SAlu ALU_ADD vF (SLit 568)) = uval rho vF + 568) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [|split].
    + fact HF (SPUle k_av (SLit 4294967295)) HkB. rewrite h_ule, uval_lit in HkB by lia.
      intros Hk. apply (tvz_in_kd rho (kept_vr ++ passed_vr) d_av 4 k_av HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32, Lib_vec_reserve.B32; lia | exact Hk].
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite E664. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Definition reo_chk (tv : list (sv * sv)) (X : list (sv * sv)) (Tb T : axst) : Prop := ltac2:(tb__ "0|2|
S1S0S2S27VTb;A1S7S95A1A3S1S0S16S29S19S4SfS28S3aA1S3cA2S19S4S6S10S3aA1S7S87S86Z2Z3dA2Z1A2A1A2S1bS4A1A3A3S5S25VTb;A1M0A1M1A2S15A3S1S0S16SabVX;S26VTb;A1A2S15A3S1S0S24Sb1VTb;VX;S3aZ4Z12A5VT;A3S1S0S16S13S25VT;A1A1S15A3S1S0S16S91G1Vtv;S30S90S11G0A1A5S15A3S0S16S8fG1A1S15A3A2A2A2A2A2A2").
Lemma SPA_reopen_lo : ltac2:(tb__ "0|3|
S14S17S2S2A2M0A1M1S14S71A1G1S24S24S3S14S36Q40A1A1S35S9fR8R6R5R4A4S2dG0S18S2S2S67S37Z10S68A2A4R9A3S0S16S8cVXGL;S5S25R7A1A1RaZ4Z12R8A6S15A3S2aS21VJAv;S74RbS30RaS76S69S15A2M2A4A1R8R6R5R4A6S2aS21VJAv;S74RcS30RbG2A4A1R8R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;FT;FTb;FX;Fbd;Ftv;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX.
  intros tv bd X Tb T rho tp w (C1 & C2 & C3 & C4 & C5 & C6 & C7) Hlin CXR Hw. rewrite <- C4.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
           tv frL bd (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 18 Tb X rho tp w frL_0 ltac:(lia) C1 ltac:(lia)
           ltac:(change (fs_frame_size 5) with 2048; lia) C2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xrs_inclb_sound _ _ C3) ltac:(rewrite C4; exact C5)); [|exact Hw].
  intros Ai rho3 tp3 md3 HF3 HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tv _ rho3 tp3 md3 HM HF3 HP0 Hav HT HTK HN HD HZ HFR C7 Hlin C6).
  - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tv X rho3 tp3 md3 4 18 HM HF3 HP0 Hav HT HTK HN HD HZ HFR CXR).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2bS24S3S14S36Q40A1A1S34S38S4S9R3A1S5S25R4A1A1A3VTR;S2aS21R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S34S34S34S35R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S34OS34S35R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2bS2bS24S24S64S14SbA1M0S14S17S24S6bA2M1A1S14S17S2S2A2M2A1S34S3S14S36Q40A1A1M3G2S2dG2R1R5A3S2dG2R2S26RbA1A3F_;Fr;S0S1fG0A1S6fRaR9R8A3S1dG0R7A2A3S0S16S6eRbRaR9R8S39G1S24S1eS24S6bA2R7A4A5S15A3S3G3VTR;S2aS21RfRdR2R1A5S6cS21ScS25RdA1A1R2R1RaA5A2Ftp1;Frho1;S14S40A1M4S65S3fS2cS21R9R8R10S18G4S89R3S8aR2R1A2A4A5R13RaR9R4R2A4R13S63S62RbRfS3eR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S24S6bG4S65S3fS3G3G4S65S3fS2dG1S18S24S6bRaR9A4R14A3S2cS21R12R11R19S18G4S89R9S8aR8R7A2A4A5R1cR13R12RaR8A4S92ScS25R1aA1A1S63S62R14R18S3eR9R13RaA3A3R19A2R8A3S2cS21R9R8ReS18G4S89R7S8aR6R5A2A4A5ReS63S62R16R1aS3eRbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sa7R17S3eRcR16RdA3R1bR1cR1dR10R1eR19RbA9S3S93R18S3eRdR17ReA3R1cR1dS25R1eA1S25R1fA1S25R11A1R1RcA9VTR;S2aS21S6dR11S63S62R19R1dS3eReR18RfA3A3R1eA2R18RdRcA5Sa8R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2aS21R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CHVR : ltac2:(tb__ "0|1|
S14S17S22S22A2M0A1S14S17G0S22A2A1S73S3S14S36Q40A1A1S72Z3R3A2VTR;S2aS21S7aVAInv;VCST;VXGL;VKc;S61R6R5A2R6R5R4S75SadS54S15S9cA3AaS9bR3R2A5S6cS21Sa2R3R2SaeVAInv;VCST;VXGL;VKc;S61S75S4aR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Definition rel_chk (L : list (Z * Z)) (E0 Er : axst) : Prop := ltac2:(tb__ "0|6|
S1S0S14SbA1S11S25VE0;A1M0A1S1cSbS58VE0;A1M1S19SbSb2S3aZ4M2Z12M3S12S5cVE0;A1A1M4SdA5S1bSbA1A3A3A3S1S0S2S27VE0;A1S7S95A1A3S1S0S16S29S19S4SfS28S3aA1S3cA2S19S4S6S10S3aA1S7S87S86Z2Z3dA2Z1A2A1A2S1bS4A1A3A3S5G0A1M5A2S15A3S1S0S16S2fS17S22S22A2SafG4SdG2G3A4VL;A3S15A3S1S0S16S81ScG0A1S8bA2S15A3S1S0S16S91G5S33S30S90G1A5S15A3S1S0S16S8fG5A1S15A3S0S24Sb0VE0;G1P6eVL;A4VEr;A3A2A2A2A2A2A2A2").
Lemma site_rel : ltac2:(tb__ "0|2|
S14S17S22S22A2A1S24S24S3S14S36Q40A1M0A1S34S9eR6R5R4A3S31R4A1S3S31R1A1S23S2dS23R1S32A3S0G0S8R4R2A2S8R9R2A2A3F_;Fv;VTR;S2aS21VJAv;S8bA1M1R9R3R7A5R6A2F_;F_;Frho1;VTR;S2aS21G1R8R6R5A5R4A2F_;F_;F_;FQ;Ftp;Frho;FEr;FE0;FL;").
Proof using ALA HCST HXGL LFSH HKc HBX TR_facts TR_pre TR_exw TR_pureP.
  intros L E0 Er rho tp Q (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8) HPHI HK.
  apply TR_facts. intros HF0.
  apply (TR_pre (fun w => exists rho1, (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v) /\ SPA segs (JAv ndA1) Er rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 4 18 (ob_cells (sh_of E0)) DUnknown] (vms md tp ms)). split.
    - split; [|intros v _; reflexivity].
      destruct Hw as [Hsm (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & HM & HT & _ & _ & (_ & _ & HZ) & _).
      pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
      destruct (lines_blk rho _ (topG (aa_geom Ai)) HF0 R7 HTK) as (_ & HiC & HcK & _ & _ & Htop).
      pose proof (lines_nz rho _ (topG (aa_geom Ai)) tvL HF0 R7 HTK HZ lines_in_tvL) as Hnz.
      pose proof (has_facts_sound rho _ _ HF0 R3) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
      pose proof (topG_range (aa_geom Ai)) as TG.
      apply (tblB_absorb_sh AInv CST XGL ALA HCST Kc FB FF BX rho0 ndA1 Ai kc rho tp tr md 0%nat 110%positive 5 120%positive g5 4 18 _ DUnknown _ HJ frL_0);
        [lia | lia | change (fs_frame_size 5) with 2048; lia | exact HG1 | exact HG2 | exact lines_in_tvL | exact Hnz | lia | exact HiC | exact HcK | exact HPHI].
    - rewrite <- R8.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL (bdA A1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 18 (ob_cells (sh_of E0)) DUnknown E0 (objs_nl E0) L rho tp tr ms md
               frL_0 ltac:(lia) R2 R1 ltac:(lia) ltac:(change (fs_frame_size 5) with 2048; lia) eq_refl R3 R4 R5); [|exact Hw].
      intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
      exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tvL (objs_nl E0) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR R7 lines_in_tvL R6). }
  apply TR_exw. intros rho1.
  apply (TR_pureP _ (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v)); [intros w [H _]; exact H|]. intros [HPHI1 HV1].
  apply (TR_pre (SPA segs (JAv ndA1) Er rho1 tp)); [intros w [_ Hw]; exact Hw|]. exact (HK rho1 HPHI1 HV1).
Qed.

Lemma site_vr : ltac2:(tb__ "0|5|
S3S14S36Q40A1M0A1M1S34S0S16S8cVXGL;S5S25S4cA1A1S47Z4Z12S9aA6S15A3S31R4A1S3G1S31R2A1M2S23S2dS23R1S32A3M3S0G0S8R5R2A2M4S8RaR2A2A3F_;Fv;VTR;S2aS21VJAv;S57A1S50R4R3A5R7A2F_;F_;Ftp';Frho';S3G1G2S23G3S0G0G4S8RbR2A2A3F_;Fv;VTR;S2aS21VJAv;S56A1S4eR4R3A5R8A2F_;F_;Ftp';Frho';S3G1G2S23G3S0G0G4S8RcR2A2A3F_;Fv;VTR;S2aS21VJAv;S55A1S4bR4R3A5R9A2F_;F_;Ftp';Frho';VTR;S2aS21VJAv;S8bA1Sa0R8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CHVR.
  intros rho tp Q CXR HPHI Kk Kg Kf.
  pose proof hv3_checks_vr as (Cxf & CEvr & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & Cpay & Cnb & Cbr & Cnp & _ & _ & CLN & CVB).

  assert (CREL : rel_chk [(32, 12)] K_vr K_vrr).
  { pose proof hv3_checks_rel as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 R8))))))). }
  apply (site_rel [(32, 12)] K_vr K_vrr rho tp Q CREL HPHI). intros rho1 HPHI1 HV1.

  set (ndv := NDA tv_vr frL bd_vr (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_vr rho1 tp)).
  { intros w Hw. rewrite <- CEvr. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) (xf_vr K_vrr) rho1 K_vrr E_vr1 tp w Cxf).
      unfold ndv, tv_vr. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_vr _ K_vrr rho1 tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ K_vrr rho1 tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. constructor; [exact (room_av_holds rho1 HF1) | constructor]. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho1 xLD <> 0 /\ uval rho1 pI < uval rho1 xLC /\ uval rho1 xLC <= uval rho1 xLK /\ 16 * uval rho1 xLK <= 4294967295
                     /\ uval rho1 xLD + 16 * uval rho1 xLK <= 2 ^ 47)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho1 Ai Hav ltac:(reflexivity) HT) as HTK. pose proof (topG_range (aa_geom Ai)) as TG.
    destruct (lines_blk rho1 _ (topG (aa_geom Ai)) HF CLN HTK) as (_ & HiC & HcK & Hk32 & _ & HdT).
    split; [|repeat split; lia].
    apply (lines_nz rho1 _ (topG (aa_geom Ai)) tv_vr HF CLN HTK HZ). unfold tv_vr. apply in_or_app. left. exact lines_in_kept_vr. }
  intros (Hdnz & HiC & HcK & Hk32 & HdT).
  unfold ndv, tv_vr.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VR.Pre_vr (ndh h0 true VR.nd0) PDk_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHVR eq_refl
           E_vr s_vr R_vr Xk_vr rho1 tp kept_vr passed_vr frL bd_vr brest_vr (AHead pH true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_vr rho1 ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HV' : forall v, In v V_B -> rw rho' v = rw rho v).
    { intros v Hv. rewrite (V_B_agree_n _ rho1 rho' CVB Hag v Hv). exact (HV1 v Hv). }
    assert (HPHI' : tblB rho').
    { apply (tblB_kept rho1 rho' (V_B_agree_n _ rho1 rho' CVB Hag)); [| exact HiC | exact HcK | exact HPHI1].
      apply (keptK_lines CST FB FF rho0 rho1 kept_vr frL rho' HK lines_in_kept_vr Hdnz); [exact HdT | unfold B32, Lib_vec_reserve.B32; lia]. }
    pose proof hv3_checks_vr_nd as (Nk & Ng & Nf & Tk0 & Tg0 & Tf0 & Bk & Bg & Bf & Tik & Tig & Tif & Reo & RBase & RHf & RXi & RSwf & RRo & RLn & Sk & Sg & Fbk & Fbg & _).
    pose proof hv3_facts_slot as [Ssk Ssg].
    cbn [PDk_vr liftPD PDh PD_vr map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite Tk0, Nk.
      apply (TR_pre (SPA segs (JAv nd_keep) T_keepS rho' tp')); [|exact (Kk rho' tp' HPHI' HV')].
      intros w Hw. rewrite <- Sk. apply (SPA_refacts_JA segs); [| exact Fbk |].
      * rewrite <- Tik. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_keep) (xfb_vr T_keep0) rho' T_keep0 B_keep tp' w Bk Hw).
      * intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. unfold inj_keep. apply Forall_app. split; [exact (slot_holds rho' _ k_av HF2 Ssk)|].
        constructor; [|constructor].
        destruct (slot_vals rho' _ k_av HF2 Ssk) as (V1 & V2 & _ & _). pose proof (uval_range rho' cnt_av) as RC.
        assert (TNZ : tnz rho' (d_av, kb 4 k_av)).
        { unfold tnz. cbn [fst]. pose proof HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (_ & _ & HZ') & _). cbn [nd_tv nd_keep] in HZ'.
          apply (tvz_in_kd rho' tv_keep d_av 4 k_av HZ'); [exact av_in_tv_keep | lia | unfold B32, Lib_vec_reserve.B32; lia | lia]. }
        pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue ALA nd_keep rho' tp' tr md (d_av, kb 4 k_av) eq_refl HJ
                      av_in_tv_keep TNZ) as TF.
        apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite Tf0, Nf.
      apply (TR_pre (SPA segs (JAv nd_fail) T_fail rho' tp')); [|exact (Kf rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo tv_fail brest_vr X_hv T_failr T_fail rho' tp' w (conj RBase (conj RHf (conj RXi (conj Reo (conj RSwf (conj RRo RLn)))))) lines_in_tv_fail CXR).
      rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fail) (xfb_vr T_fail0) rho' T_fail0 B_fail tp' w Bf Hw).
    +
      rewrite Tg0, Ng.
      apply (TR_pre (SPA segs (JAv nd_grown) T_grownS rho' tp')); [|exact (Kg rho' tp' HPHI' HV')].
      intros w Hw. rewrite <- Sg. apply (SPA_refacts_JA segs); [| exact Fbg |].
      * rewrite <- Tig. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_grown) (xfb_vr T_grown0) rho' T_grown0 B_grown tp' w Bg Hw).
      * intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. exact (slot_holds rho' _ vKg HF2 Ssg).
Qed.

Lemma site_mc : ltac2:(tb__ "0|5|
S14S17S2S2A2M0A1M1S14S71A1G1S24S24S3S14S36Q40A1M2A1M3S34S9dR8R6R5R4A4S2dG0S18S2S2S67S37Z10S68A2A4R9A3S0S16S8cVXGL;S5S25R7A1A1RaZ4Z12R8A6S15A3S31R6A1S3G3S31R2A1S23S2dS23R1S32A3S0G2S8R5R2A2S8RcR2A2A3F_;Fv;VTR;S2aS21VJAv;S74R10S30RfS76S69S15A2M4A4A1RcR4R3A5R9A2F_;F_;Ftp';Frho';VTR;S2aS21VJAv;S74RdS30RcG4A4A1RaR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;FT;FXc;FX;Fbd;Ftv;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_pre.

  intros tv bd X Xc T rho tp Q HC Hlin CXR HPHI HK.
  apply (TR_pre (SPA segs (JAv (NDA tv frL bd (AHead pH true))) T rho tp)); [|exact (HK rho tp HPHI (fun v _ => eq_refl))].
  intros w Hw. exact (SPA_reopen_lo tv bd X Xc T rho tp w HC Hlin CXR Hw).
Qed.
End X.
End Sum.
