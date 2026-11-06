(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rw"; "ss_facts"; "sprop"; "holds"; "sobj"; "ss_next"; "SLit"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "true"; "bool"; "app"; "Some"; "cons"; "nil"; "option"; "snd"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tblB"; "V_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "xLK"; "pH"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4"; "kept_o1"; "R_o1"; "X_1"; "nd_op1"; "tv_op0"; "tv_op1"; "E_o1c"; "PDk_o1"; "T_op0"; "T_op0r"; "T_op1"; "T_op1r"; "Xk_o1"; "nd_op0"; "passed_o1"; "s_o1c"; "tv_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4p"; "kept_o3"; "E_o3c"; "R_o3"; "X_3"; "payX_o3"; "tv_p0"; "tv_p1"; "PDk_o3"; "T_p0"; "T_p0r"; "T_p1"; "T_p1r"; "Xk_o3"; "nd_p0"; "nd_p1"; "passed_o3"; "payY_o3"; "s_o3c"; "tv_o3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf5.OP1P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf5.OP3P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "PTrue"; "ndesc"; "ANone"; "JA_pre"; "NDA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "tvinA"; "AHead"; "JA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BXok_d"; "bd_nn"; "bd_wpos"; "bxt"; "pay_sem"; "pay_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4w"; "PreR"; "LR"; "E_o3"; "R_w"; "s_w"; "w_chk"; "w_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "h0"; "nd_keep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd";
"tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3m"; "E_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4.OP1"; "PD_op"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4p.OP3"; "PD_op"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "JL_pure"; "J_pure_pre"; "alloc_lawsA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hvpk Lib_load_obj_hv2 Lib_load_obj_hv_pf1 Lib_load_obj_hv3 Lib_load_obj_hv3m Lib_load_obj_hv3e Lib_load_obj_loopE Lib_load_obj_hv3f Lib_load_obj_hv_pf3 Lib_load_obj_hv_pf4 Lib_load_obj_hv4 Lib_load_obj_hv4w Lib_load_obj_hv4p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Module OP1P. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_opt_push1_pf. End OP1P.
Lemma HamC_o1 : nd_am OP1.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_o1 : ltac2:(tb__ "0|1|
S2cSaS16S61A2M0G0S19S66S6aS13S16S61R1A3A1S62A3Ld;S98A3"). Proof. repeat constructor. Qed.
Lemma P0_op_mono : ltac2:(tb__ "0|2|
S9SaS1cS1cA2M0A1M1G1S9SaG0S1cA2A1S1G0S1eG0R1R5A3S1eG0R2R5A3F_;Fbn;S5eR5R3R2A3S5eR5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.
Lemma lines_in_kept_o1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S3aA3").
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hv4_checks_o1_nd)))))))))))). Qed.
Lemma lines_in_tv_o1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S4aA3").
Proof. unfold tv_o1. apply in_or_app. left. exact lines_in_kept_o1. Qed.
Lemma lines_in_tv_op1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S3fA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_tv_op0 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S3eA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.

Module OP3P. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_opt_push3_pf. End OP3P.
Lemma HamC_o3 : nd_am OP3.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_o3 : ltac2:(tb__ "0|1|
S2cSaS16S61A2M0G0S19S66S6aS13S16S61R1A3A1S62A3Ld;S9bA3"). Proof. repeat constructor. Qed.
Lemma P0_op3_mono : ltac2:(tb__ "0|2|
S9SaS1cS1cA2M0A1M1G1S9SaG0S1cA2A1S1G0S1eG0R1R5A3S1eG0R2R5A3F_;Fbn;S5fR5R3R2A3S5fR5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.
Lemma lines_in_kept_o3 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S4bA3").
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hv4_checks_o3_nd)))))))))))). Qed.
Lemma lines_in_tv_o3 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S5dA3").
Proof. unfold tv_o3. apply in_or_app. left. exact lines_in_kept_o3. Qed.
Lemma lines_in_tv_p1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S51A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_tv_p0 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S29S28Z10S2aA2A4S50A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.

Lemma pay_okF_split_sem : ltac2:(tb__ "0|1|
S1OF_;S9S4A1S0S1cS9S6fA1M0G0G0G0G0S19SdS92R5SeS6fR3R2A3A2ScA3S19SdS92SeS6fR4R2A3R5A2ScA3S19SdS72R5A1ScA3S19SdS72R4A1ScA3S87Z0RaA2S1S2cS4S5R1A1ReA3S71R9R2A2S74R3RfReRaR9A5F_;F_;Frho;S75RfReRdRcRbRaA6F_;F_;F_;F_;F_;F_;FY;FX;Fcommon;Fbto;Fbfrom;FcostK;FcostV;Ffacts;Fpre;").
Proof.
  intros pre facts costV costK bfrom bto common X Y HP1 HP2 Hwc Hwy Hk Hsem.
  pose proof (bd_permb_sound _ _ HP1) as P1. pose proof (bd_permb_sound _ _ HP2) as P2.
  split; [|split; [exact Hk|]].
  - unfold bd_wpos in *. apply forallb_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hwc it Hin) | exact (proj1 (forallb_forall _ _) Hwy it Hin)].
  - intros rho HF Hpre Hwf Hnf.
    assert (Hn2 : bd_nn (common ++ X) rho).
    { unfold bd_nn in *. apply Forall_forall. intros it Hit. apply (proj1 (Forall_forall _ _) Hnf). eapply Permutation_in; [apply Permutation_sym; exact P1 | exact Hit]. }
    unfold bd_nn in Hn2. apply Forall_app in Hn2 as [Hnc Hnx].
    destruct (Hsem rho HF Hnx) as (Q1 & Q2 & Q6).
    unfold pay_sem. rewrite (bsumV_perm bfrom (common ++ X) rho P1), (bsumK_perm bfrom (common ++ X) rho P1).
    rewrite <- (bsumV_perm (common ++ Y) bto rho P2), <- (bsumK_perm (common ++ Y) bto rho P2).
    rewrite !bsumV_app, !bsumK_app. split; [lia|]. split; [lia|].
    unfold bd_nn. apply Forall_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) Hnc it Hin) | exact (proj1 (Forall_forall _ _) Q6 it Hin)].
Qed.

Lemma pay_o3 : ltac2:(tb__ "0|1|
S1S2cS4S5R1A1S3S17S4cA1A1A3S71S4fR2A2S74R3S8Z0M0A1G0S4fS5bA5F_;F_;Fr;").
Proof.
  intros r HF Hnn.
  pose proof hv4_checks_o3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CNV & _).
  pose proof (holds_mem _ _ _ HF CNV) as FN. rewrite h_ule, uval_lit in FN by lia.
  pose proof (uval_range r c_av) as RC. pose proof (uval_range r k_acol) as RK.
  assert (E3 : uval r (SMd M_MUL (SLit 3) c_av) = 3 * uval r c_av) by (apply uval_mul_lit; lia).
  assert (E2 : uval r (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 2)) = 3 * uval r c_av + 2).
  { rewrite uval_add_small by (rewrite E3, uval_lit by lia; lia). rewrite E3, uval_lit by lia. reflexivity. }
  assert (E5 : uval r (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 5)) = 3 * uval r c_av + 5).
  { rewrite uval_add_small by (rewrite E3, uval_lit by lia; lia). rewrite E3, uval_lit by lia. reflexivity. }
  assert (A2 : uval r (SMd M_MUL (SLit 4) (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 2))) = 4 * (3 * uval r c_av + 2)).
  { rewrite uval_mul_lit by (rewrite ?E2; lia). rewrite E2. reflexivity. }
  assert (A5 : uval r (SMd M_MUL (SLit 4) (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 5))) = 4 * (3 * uval r c_av + 5)).
  { rewrite uval_mul_lit by (rewrite ?E5; lia). rewrite E5. reflexivity. }
  pose proof (uval_range r vLEN) as RL0. pose proof (uval_range r pNX) as RN0.
  unfold bd_nn, payX_o3 in Hnn. apply Forall_cons_iff in Hnn as [N1 N2]. apply Forall_cons_iff in N2 as [N2 _].
  unfold phi_old, LA, A1 in N1, N2. cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c] in N1, N2. rewrite A2 in N1.
  unfold pay_sem, payX_o3, payY_o3, phi_old, phi_new, LA, A1, bd_nn.
  cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite A2, A5. rewrite (uval_lit r 0) by lia.
  split; [lia|]. split; [lia|].
  constructor; [|constructor; [|constructor]]; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?A5; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S76S1S9S22Q40A1A1S2eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa3S15VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1cS86VCST;R1A2S1aS87Z0R2A2S88R2S95A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1cS86VXGL;R1A2S1aS87Z0R2A2S88R2S95A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S1cS96R1A1S86VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S9SaSaS1cS1cA2S1cA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S1OFr;") := ltac2:(tb__ "0|0|
S9eVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S6dVAInv;VCST;VXGL;S7bVKc;Vrho0;VP0;VFB;VFF;VBX;S60Vnd;Ac").

Lemma HIN_o1 : ltac2:(tb__ "0|1|
S1S39S76S1S9S22Q40A1A1S2eS2cS4S5R6A1S3S17S40A1A1A3VP0;Vrho0;A1S83S7bVrho0;R8A3VAInv;R7R6R5R4A4S65Vrho0;R8A2S8cRbS78S77R9A1A1A2S67VFB;RaA2S68VFF;RbA2S6bVFB;RcReSeSaS0S0A2S3aS48A3M0A4S8dRfG0A2S8eR10G0A2S69VFF;RfR11S23A4S1aS90VCST;Vrho0;VFB;VFF;R12S3aS23S3bA8S1aS91VCST;VXGL;Vrho0;VFB;VFF;R12S3aS23S46A9S5eS8bVFB;R12S3aA3S8fVFF;R12S23A3S31S30R12S3bR11A3S49A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof hv4_checks_o1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN & _ & W12 & W36 & W33 & W34).
  assert (HNk : tvinA FB Ai rho kept_o1) by (apply (tvinA_sublist FB Ai rho (kept_o1 ++ passed_o1)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_o1) by (exact (tvd_app_l rho kept_o1 passed_o1 HD)).
  assert (HZk : tvz rho kept_o1) by (apply (tvz_sublist rho (kept_o1 ++ passed_o1)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF AInv CST ALA HCST FB FF rho0 Ai rho _ kept_o1 R_o1 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CLN lines_in_kept_o1 CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_o1 Xk_o1 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold OP1P.P0_op. rewrite !rw_call'. rewrite W12, W36, W33, W34.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    assert (EA : forall k, 0 <= k <= 2048 -> uval rho (SAlu ALU_ADD vF (SLit k)) = uval rho vF + k).
    { intros k Hk. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
    unfold alA. rewrite !EA by lia. unfold OP1.CM.
    repeat split; exists (uval rho vF), 2048, (uval rho vFL); (split; [exact HinF | lia]).
Qed.

Lemma HIN_o3 : ltac2:(tb__ "0|1|
S1S39S76S1S9S22Q40A1A1S2eS2cS4S5R6A1S3S17S4cA1A1A3VP0;Vrho0;A1S83S7bVrho0;R8A3VAInv;R7R6R5R4A4S65Vrho0;R8A2S8cRbS78S77R9A1A1A2S67VFB;RaA2S68VFF;RbA2S6bVFB;RcReSeSaS0S0A2S4bS5aA3M0A4S8dRfG0A2S8eR10G0A2S69VFF;RfR11S23A4S1aS90VCST;Vrho0;VFB;VFF;R12S4bS23S4dA8S1aS91VCST;VXGL;Vrho0;VFB;VFF;R12S4bS23S57A9S5fS8bVFB;R12S4bA3S8fVFF;R12S23A3S31S30R12S4dR11A3S5cA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof hv4_checks_o3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN & _ & W12 & W36 & W33 & W34 & _).
  assert (HNk : tvinA FB Ai rho kept_o3) by (apply (tvinA_sublist FB Ai rho (kept_o3 ++ passed_o3)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_o3) by (exact (tvd_app_l rho kept_o3 passed_o3 HD)).
  assert (HZk : tvz rho kept_o3) by (apply (tvz_sublist rho (kept_o3 ++ passed_o3)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF AInv CST ALA HCST FB FF rho0 Ai rho _ kept_o3 R_o3 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CLN lines_in_kept_o3 CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_o3 Xk_o3 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold OP3P.P0_op. rewrite !rw_call'. rewrite W12, W36, W33, W34.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    assert (EA : forall k, 0 <= k <= 2048 -> uval rho (SAlu ALU_ADD vF (SLit k)) = uval rho vF + k).
    { intros k Hk. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
    unfold alA. rewrite !EA by lia. unfold OP3.CM.
    repeat split; exists (uval rho vF), 2048, (uval rho vFL); (split; [exact HinF | lia]).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S20S16S1S9S22Q40A1A1S26S2cS4S5R3A1S3S17R4A1A1A3VTR;S1fS15R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S26S26S26S27R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S26OS26S27R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S20S20S16S16S32S9S6A1M0S9SaS16S33A2M1A1S9SaS0S0A2M2A1S26S1S9S22Q40A1A1M3G2S1eG2R1R5A3S1eG2R2S18RbA1A3F_;Fr;S19S12G0A1S36RaR9R8A3SfG0R7A2A3S19SdS35RbRaR9R8S2dG1S16S14S16S33A2R7A4A5ScA3S1G3VTR;S1fS15RfRdR2R1A5S34S15S7S17RdA1A1R2R1RaA5A2Ftp1;Frho1;S9S2fA1M4S39S2eS21S15R9R8R10SbG4S79R3S7aR2R1A2A4A5R13RaR9R4R2A4R13S31S30RbRfS38R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S16S33G4S39S2eS1G3G4S39S2eS1eG1SbS16S33RaR9A4R14A3S21S15R12R11R19SbG4S79R9S7aR8R7A2A4A5R1cR13R12RaR8A4S83S7S17R1aA1A1S31S30R14R18S38R9R13RaA3A3R19A2R8A3S21S15R9R8ReSbG4S79R7S7aR6R5A2A4A5ReS31S30R16R1aS38RbR15RcA3A3R1bA2R15RaR9R8R6A6S1aS9fR17S38RcR16RdA3R1bR1cR1dR10R1eR19RbA9S1S84R18S38RdR17ReA3R1cR1dS17R1eA1S17R1fA1S17R11A1R1RcA9VTR;S1fS15S37R11S31S30R19R1dS38ReR18RfA3A3R1eA2R18RdRcA5Sa0R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1fS15R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CHOP1 : ltac2:(tb__ "0|1|
S9SaS1cS1cA2M0A1S9SaG0S1cA2A1S73S1S9S22Q40A1A1S70Z4R3A2VTR;S1fS15S63VAInv;VCST;VXGL;VKc;S5eR6R5A2R6R5R4S60S93S89ScS9aA3AaS99R3R2A5S34S15S85R3R2S94VAInv;VCST;VXGL;VKc;S5eS60S41R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Lemma site_o1 : ltac2:(tb__ "0|7|
S1S9S22Q40A1M0A1M1S26S19SdS6eVXGL;S3S17S45A1A1S3fZ4M2Z12M3S3cA6ScA3S19SdS6eVXGL;S3S17S43A1A1S3eG2G3S3cA6ScA3S24R5A1S1G1S24R2A1M4S1dS1eS1dR1S25A3M5S19G0S2R5R2A2M6S2RbR2A2A3F_;Fv;VTR;S1fS15VJAv;S3dA1S44R4R3A5R8A2F_;F_;Ftp';Frho';S1G1G4S1dG5S19G0G6S2RcR2A2A3F_;Fv;VTR;S1fS15VJAv;S47A1S42R4R3A5R9A2F_;F_;Ftp';Frho';VTR;S1fS15VJAv;S8aA1S97R8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CHOP1.
  intros rho tp Q CXR1 CXR0 HPHI K1 K0.
  pose proof hv4_checks_o1 as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & _ & _ & CLN & CVB & _).

  assert (CREL : rel_chkG tv_keep bd_keep [(64, 4); (80, 4)] E_o1 E_o1r).
  { pose proof hv4_checks_rel as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 R8))))))). }
  unfold nd_keep.
  apply (site_relG AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 TR TR_facts TR_pre TR_exw TR_pureP
           tv_keep bd_keep [(64, 4); (80, 4)] E_o1 E_o1r rho tp Q CREL lines_in_tv_keep HPHI). intros rho1 HPHI1 HV1.

  set (ndv := NDA tv_o1 frL bd_o1 (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_o1c rho1 tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) (xf_o1 E_o1r) rho1 E_o1r E_o1c tp w Cxf).
    unfold ndv. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL bd_keep bd_o1 _ E_o1r rho1 tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_keep _ frL bd_keep _ E_o1r rho1 tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho1 xLD <> 0 /\ uval rho1 pI < uval rho1 xLC /\ uval rho1 xLC <= uval rho1 xLK /\ 16 * uval rho1 xLK <= 4294967295
                     /\ uval rho1 xLD + 16 * uval rho1 xLK <= 2 ^ 47)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho1 Ai Hav ltac:(reflexivity) HT) as HTK. pose proof (topG_range (aa_geom Ai)) as TG.
    destruct (lines_blk rho1 _ (topG (aa_geom Ai)) HF CLN HTK) as (_ & HiC & HcK & Hk32 & _ & HdT).
    split; [|repeat split; lia].
    exact (lines_nz rho1 _ (topG (aa_geom Ai)) tv_o1 HF CLN HTK HZ lines_in_tv_o1). }
  intros (Hdnz & HiC & HcK & Hk32 & HdT).
  unfold ndv, tv_o1.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX OP1P.P0_op PTrue (fun _ H => H) (fun _ _ _ H => H)
           OP1.Pre_op (ndh h0 true OP1.nd0) PDk_o1 NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHOP1 eq_refl
           E_o1c s_o1c R_o1 Xk_o1 rho1 tp kept_o1 passed_o1 frL bd_o1 brest_o1 (AHead pH true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. unfold payA. apply (pay_okF_split _ _ _ _ bd_o1 _ payC_o1 payX_o1 payY_o1 PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_o1 rho1 ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HV' : forall v, In v V_B -> rw rho' v = rw rho v).
    { intros v Hv. rewrite (V_B_agree_n _ rho1 rho' CVB Hag v Hv). exact (HV1 v Hv). }
    assert (HPHI' : tblB rho').
    { apply (tblB_kept rho1 rho' (V_B_agree_n _ rho1 rho' CVB Hag)); [| exact HiC | exact HcK | exact HPHI1].
      apply (keptK_lines CST FB FF rho0 rho1 kept_o1 frL rho' HK lines_in_kept_o1 Hdnz); [exact HdT | unfold B32, Lib_vec_reserve.B32; lia]. }
    pose proof hv4_checks_o1_nd as (N1 & N0 & T10 & T00 & B1 & B0 & Ti1 & Ti0 & REO1 & REO0 & _).
    cbn [PDk_o1 liftPD PDh OP1.PD_op map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite T10, N1.
      apply (TR_pre (SPA segs (JAv nd_op1) T_op1 rho' tp')); [|exact (K1 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_op1 bd_op1 X_1 T_op1r T_op1 rho' tp' w REO1 lines_in_tv_op1 CXR1).
      rewrite <- Ti1. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_op1) (xfb_o1 T_op1_0) rho' T_op1_0 B_op1 tp' w B1 Hw).
    +
      rewrite T00, N0.
      apply (TR_pre (SPA segs (JAv nd_op0) T_op0 rho' tp')); [|exact (K0 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_op0 brest_o1 X_1 T_op0r T_op0 rho' tp' w REO0 lines_in_tv_op0 CXR0).
      rewrite <- Ti0. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_op0) (xfb_o1 T_op0_0) rho' T_op0_0 B_op0 tp' w B0 Hw).
Qed.

Hypothesis CMEMCPYR : ltac2:(tb__ "0|2|
S76S1S9S22Q40A1A1M0VTR;S1fS15S1G0S9S2fA1S2eS1aSa2VAInv;R7VKc;R4R3R2R1A7S1bA2Lm;Lt;Lp;Lr;S7cR2R1A5S34S15S85R2R1S10SaS16S33A2M1SbS16S33S7dSa1VAInv;VCST;VXGL;R3VKc;A5A4S11G1A1A3A5A2Ftp1;Frho1;FAi;").
Lemma w_ok_ent : ltac2:(tb__ "0|3|
S16S19SdS82R1A1ScA3S1aS19S12S9S6A1M0A1S36R2S7cS80R2A1M1A3SfG0S7fR2A1M2A2A3S19SdS35R2S7cG1G2S10S16S7dS11S16A1A3A5ScA3A2F_;FE;").
Proof using . intros E H. unfold w_ok, R_w in *. destruct (entails_frA E PreR (s_w E)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.
Lemma site_w : ltac2:(tb__ "0|4|
S9SaS0S0A2M0A1S9S6fA1S16S16S16S16S16S16S1S9S22Q40A1M1A1M2S26S81RbRaR9R8R7R6R5R4A8S1eG0SbS0S0S29S28Z10S2aA2A4RcA3S24R5A1S1G2S24R2A1S1dS1eS1dR1S25A3S19G1S2R5R2A2S2RbR2A2A3F_;Fv;VTR;S1fS15VJAv;S64R12S23R11S6cS2bScA2M3A4A1RbR4R3A5R8A2F_;F_;Ftp';Frho';VTR;S1fS15VJAv;S64RfS23ReG3A4A1RdR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;FT;FTb;FT0;FE;FEr;FL;Fbd;Ftv;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CMEMCPYR.
  intros tv bd L Er E T0 Tb T rho tp Q
    (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & Cxf & Cok & Cta & Cnp & Cnb & Cbb & Cwp & Cpp & CR & CX & CLN & CVE & CT0 & CTb & CT & _) Hlin HPHI HK.
  destruct (w_ok_ent E Cok) as [Cent Cchk].
  set (nd := NDA tv frL bd (AHead pH true)).
  assert (CREL : rel_chkG tv bd [(96, 12); (128, 12)] L Er) by (exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 R8)))))))).
  apply (site_relG AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 TR TR_facts TR_pre TR_exw TR_pureP
           tv bd [(96, 12); (128, 12)] L Er rho tp Q CREL Hlin HPHI). intros rho1 HPHI1 HV1.
  apply (TR_pre (SPA segs (JAv nd) E rho1 tp)). { intros w Hw. exact (SPA_axforms segs (JAv nd) (xf_w Er) rho1 Er E tp w Cxf Hw). }
  apply TR_facts. intros HF1.
  apply (TR_pureP _ (uval rho1 xLD <> 0 /\ uval rho1 pI < uval rho1 xLC /\ uval rho1 xLC <= uval rho1 xLK /\ uval rho1 (kb 16 xLK) = 16 * uval rho1 xLK)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv nd] in HZ.
    pose proof (T_of_TPA NP rho0 rho1 Ai Hav ltac:(reflexivity) HT) as HTK.
    destruct (lines_blk rho1 _ (topG (aa_geom Ai)) HF1 CLN HTK) as (_ & HiC & HcK & _ & EK & _).
    split; [exact (lines_nz rho1 _ (topG (aa_geom Ai)) tv HF1 CLN HTK HZ Hlin) | split; [exact HiC | split; [exact HcK | exact EK]]]. }
  intros (Hdnz & HiC & HcK & EK).
  apply (purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           (fun _ _ => True) PreR [LR] E (s_w E) (R_w E) rho1 tp nd bd Q).
  - intros Ai rho2 tp2. cbn [map]. exact (CMEMCPYR Ai rho2 tp2).
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - cbn [nd_bd nd]. apply payA_same. exact Cwp.
  - exact Cpp.
  - exact (site_rt_lo AInv CST XGL ALA HCST HXlits FB FF rho0 E (s_w E) (R_w E) rho1 tv bd (AHead pH true) CR CX CLN Hlin).
  - intros Ai tr ms md _ _ _. exact I.
  - intros L' rho2 tp2 HL Hag HKR. destruct HL as [<-|[]]. cbn [nd_tv nd_fr nd_am nd].
    change (T_afterA PreR E (s_w E) (R_w E) LR) with (T_wc E). rewrite CT0.
    assert (HV2 : forall v, In v V_B -> rw rho2 v = rw rho v).
    { intros v Hv. rewrite (V_B_agree_n _ rho1 rho2 CVE Hag v Hv). exact (HV1 v Hv). }
    apply (TR_pre (SPA segs (JAv nd) T rho2 tp2)).
    { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv nd) (xfb_w T0) rho2 T0 Tb tp2 w CTb Hw). }
    apply (HK rho2 tp2); [|exact HV2].
    apply (tblB_kept rho1 rho2 (V_B_agree_n _ rho1 rho2 CVE Hag)); [| exact HiC | exact HcK | exact HPHI1].
    intros z Hz. apply (HKR (xLD, kb 16 xLK) z Hlin); [unfold tnz; cbn [fst]; exact Hdnz|].
    unfold tvv. cbn [fst snd]. change (bv_unsigned (eval rho1 xLD)) with (uval rho1 xLD). change (bv_unsigned (eval rho1 (kb 16 xLK))) with (uval rho1 (kb 16 xLK)).
    rewrite EK. exact Hz.
Qed.

Hypothesis CHOP3 : ltac2:(tb__ "0|1|
S9SaS1cS1cA2M0A1S9SaG0S1cA2A1S73S1S9S22Q40A1A1S70Z4R3A2VTR;S1fS15S63VAInv;VCST;VXGL;VKc;S5fR6R5A2R6R5R4S60S93S89ScS9dA3AaS9cR3R2A5S34S15S85R3R2S94VAInv;VCST;VXGL;VKc;S5fS60S52R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Lemma site_o3 : ltac2:(tb__ "0|7|
S1S9S22Q40A1M0A1M1S26S19SdS6eVXGL;S3S17S56A1A1S51Z4M2Z12M3S4eA6ScA3S19SdS6eVXGL;S3S17S54A1A1S50G2G3S4eA6ScA3S24R5A1S1G1S24R2A1M4S1dS1eS1dR1S25A3M5S19G0S2R5R2A2M6S2RbR2A2A3F_;Fv;VTR;S1fS15VJAv;S59A1S55R4R3A5R8A2F_;F_;Ftp';Frho';S1G1G4S1dG5S19G0G6S2RcR2A2A3F_;Fv;VTR;S1fS15VJAv;S58A1S53R4R3A5R9A2F_;F_;Ftp';Frho';VTR;S1fS15VJAv;S3dA1S7eR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_pureP TR_callP CHOP3.
  intros rho tp Q CXR1 CXR0 HPHI K1 K0.
  pose proof hv4_checks_o3 as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & PP1 & PP2 & PWc & PWy & _ & Cnb & Cbr & Cnp & _ & _ & CLN & CVB & _).
  set (ndv := NDA tv_o3 frL bd_o3 (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_o3c rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) (xf_o3 E_o3) rho E_o3 E_o3c tp w Cxf).
    unfold ndv. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL bd_op1 bd_o3 _ E_o3 rho tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_op1 _ frL bd_op1 _ E_o3 rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0 /\ uval rho pI < uval rho xLC /\ uval rho xLC <= uval rho xLK /\ 16 * uval rho xLK <= 4294967295
                     /\ uval rho xLD + 16 * uval rho xLK <= 2 ^ 47)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK. pose proof (topG_range (aa_geom Ai)) as TG.
    destruct (lines_blk rho _ (topG (aa_geom Ai)) HF CLN HTK) as (_ & HiC & HcK & Hk32 & _ & HdT).
    split; [|repeat split; lia].
    exact (lines_nz rho _ (topG (aa_geom Ai)) tv_o3 HF CLN HTK HZ lines_in_tv_o3). }
  intros (Hdnz & HiC & HcK & Hk32 & HdT).
  unfold ndv, tv_o3.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX OP3P.P0_op PTrue (fun _ H => H) (fun _ _ _ H => H)
           OP3.Pre_op (ndh h0 true OP3.nd0) PDk_o3 NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHOP3 eq_refl
           E_o3c s_o3c R_o3 Xk_o3 rho tp kept_o3 passed_o3 frL bd_o3 brest_o3 (AHead pH true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. unfold payA.
    apply (pay_okF_split_sem _ _ (SLit 0) 0 bd_o3 _ payC_o3 payX_o3 payY_o3 PP1 PP2 PWc PWy (Z.le_refl 0)). intros r HFr Hnn. exact (pay_o3 r HFr Hnn).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_o3 rho ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HV' : forall v, In v V_B -> rw rho' v = rw rho v) by (exact (V_B_agree_n _ rho rho' CVB Hag)).
    assert (HPHI' : tblB rho').
    { apply (tblB_kept rho rho' (V_B_agree_n _ rho rho' CVB Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_o3 frL rho' HK lines_in_kept_o3 Hdnz); [exact HdT | unfold B32, Lib_vec_reserve.B32; lia]. }
    pose proof hv4_checks_o3_nd as (N1 & N0 & T10 & T00 & B1 & B0 & Ti1 & Ti0 & REO1 & REO0 & _).
    cbn [PDk_o3 liftPD PDh OP3.PD_op map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    + rewrite T10, N1.
      apply (TR_pre (SPA segs (JAv nd_p1) T_p1 rho' tp')); [|exact (K1 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_p1 bd_p1 X_3 T_p1r T_p1 rho' tp' w REO1 lines_in_tv_p1 CXR1).
      rewrite <- Ti1. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p1) (xfb_o3 T_p1_0) rho' T_p1_0 B_p1 tp' w B1 Hw).
    + rewrite T00, N0.
      apply (TR_pre (SPA segs (JAv nd_p0) T_p0 rho' tp')); [|exact (K0 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_p0 brest_o3 X_3 T_p0r T_p0 rho' tp' w REO0 lines_in_tv_p0 CXR0).
      rewrite <- Ti0. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p0) (xfb_o3 T_p0_0) rho' T_p0_0 B_p0 tp' w B0 Hw).
Qed.
End X.
End Sum.
