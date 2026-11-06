(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "cons"; "bool"; "fst"; "app"; "nil"; "Some"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "holds"; "ss_facts"; "ss_next"; "SLit"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "JA"; "TPA"; "fbinA"; "ffinA"; "frinA"; "ok_frameKA"; "tvinA"; "@Corelib.Init.Logic"; "and"; "eq"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af.HFI"; "P0_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hf"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af"; "kept_f"; "PDk_f"; "E_f"; "R_f"; "T_f_ok"; "payX_f"; "E_f1"; "Xk_f"; "passed_f"; "payY_f"; "room_f"; "s_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_nn"; "BXok_d"; "bitem"; "bxt"; "bd_wpos"; "bsumK"; "bsumV"; "pay_sem"; "AMin"; "aval"; "pay_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af.HF"; "Pre_hf"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af_eqs"; "Xs_f"; "Ys_f"; "cutsQ"; "Lok_f"; "nd_f_okX"; "rates_f"; "s_latch_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary";
"agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_af Lib_load_obj_af_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S2dS3S5S1A1M0S10OF_;M1A2M2G2S3aSaG0G1R1A3SfG0G1R1A3A2Lp;S55A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.
Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.

Lemma pay_okF_split_semF : ltac2:(tb__ "0|1|
S10OF_;S5S12A1S11S0S5S5fA1M0G0G0G0G0S2aS9S7fR5SbS5fR3R2A3A2S7A3S2aS9S7fSbS5fR4R2A3R5A2S7A3S2aS9S61R5A1S7A3S2aS9S61R4A1S7A3S2bZ0RaA2S10S2dS12S13R1A1ReA3S5dR9R2A2S64R3RfReRaR9A5F_;F_;Frho;S67RfReRdRcRbRaA6F_;F_;F_;F_;F_;F_;FY;FX;Fcommon;Fbto;Fbfrom;FcostK;FcostV;Ffacts;Fpre;").
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

Lemma room_f_holds : ltac2:(tb__ "0|0|
S10S2dS12S13R1A1S14S19S4fA1A1A3S2dS12S13R2A1S53A3F_;Fr;").
Proof.
  intros r HF.
  fact HF (SPUle (SVar 480) (SVar 476)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2. fact HF (SPUle (SVar 14) (SLit 67108864)) F3.
  fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 580) (SMd M_MUL (SLit 3) (SVar 490))) F5. fact HF (SPUle (SVar 590) (SMd M_MUL (SLit 37) (SVar 490))) F6.
  fact HF (SPUle (SVar 422) (SVar 580)) F7. fact HF (SPUle (SVar 480) (SLit 67108864)) F8. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 480) (SVar 481))) F10.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10. rewrite uval_lit in F3, F8, F9 by lia.
  pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 580)) as R580. pose proof (uval_range r (SVar 590)) as R590. pose proof (uval_range r (SVar 422)) as R422.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2, F10.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  assert (M3 : uval r (SMd M_MUL (SLit 3) (SVar 490)) = 3 * uval r (SVar 490)) by (apply uval_mul_lit; lia). rewrite M3 in F5.
  assert (M37 : uval r (SMd M_MUL (SLit 37) (SVar 490)) = 37 * uval r (SVar 490)) by (apply uval_mul_lit; lia). rewrite M37 in F6.
  assert (K1 : forall k e, 0 <= k <= 64 -> uval r e <= 2 ^ 32 -> uval r (SMd M_MUL (SLit k) e) = k * uval r e) by (intros k e Hk He; pose proof (uval_range r e); apply uval_mul_lit; [lia | nia]).
  unfold room_f.
  constructor; [apply (proj2 (h_ule _ _ _))|constructor; [apply (proj2 (h_ule _ _ _))|constructor; [apply (proj2 (h_ule _ _ _))|constructor]]].
  - rewrite uval_add_small; rewrite !K1, ?E2 by lia; [|lia]. rewrite uval_add_small; rewrite ?K1, ?uval_lit by lia; lia.
  - rewrite uval_add_small; rewrite !K1, ?E2 by lia; [|lia]. rewrite uval_add_small; rewrite ?K1, ?uval_lit by lia; lia.
  - rewrite uval_add_small; rewrite !K1, ?E2 by lia; [|lia]. rewrite uval_add_small; rewrite ?K1, ?uval_lit by lia; lia.
Qed.

Lemma pay_site_f : ltac2:(tb__ "0|1|
S10S2dS12S13R1A1S14S19S4bA1A1A3S5dS4eR2A2S64R3S16Z0M0A1G0S4eS52A5F_;F_;Fr;").
Proof.
  intros r HF _.
  fact HF (SPUle (SVar 480) (SVar 476)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2. fact HF (SPUle (SVar 14) (SLit 67108864)) F3.
  fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 480) (SVar 481))) F10.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F8. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  rewrite h_ule in F1, F2, F3, F4, F8, F9, F10. rewrite uval_lit in F3, F8, F9 by lia.
  pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 14)) as R14.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2, F10.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  unfold pay_sem. rewrite uval_lit by lia.
  assert (EY : payY_f = [LAr_f; BI 768 0 [(1, ASv (SAlu ALU_ADD (SVar 480) (SVar 481))); (-1, ASv (SVar 476))] 0]) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  rewrite EY. unfold payX_f, LAr_f, LA, A1, HF.cVF, pLNL, pNX, vLEN.
  cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite E2.
  split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?E2; lia.
Qed.

Lemma amin1_rng : ltac2:(tb__ "0|3|
S10S11S29S2bZ0M0S66R2S65R1Z1M1G0G1A4A2M2A2S2bG2G1A2A2Fe;Fr;").
Proof. intros r e. cbn [aval]. lia. Qed.

Lemma pay_f : ltac2:(tb__ "0|0|
S10S2dS12S13R1A1S14S19S4dA1A1A3S5dS71R2A2S29S2bS63S72R3A2S63S71R3A2A2S29S2bS62S72R3A2S62S71R3A2A2S5dS72R3A2A2A2F_;F_;Fr;").
Proof.
  intros r HF _. pose proof af_checks_pay as (_ & _ & _ & EX & EY & _). rewrite EX, EY.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 770) (SAlu ALU_ADD (SVar 480) (SVar 481))) F6. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  fact HF (SPUle (SAlu ALU_ADD (SVar 784) (SVar 476)) (SVar 770)) PA1. fact HF (SPUle (SVar 476) (SVar 770)) F8.
  fact HF (SPUle (SVar 784) (SVar 785)) B1. fact HF (SPUle (SVar 785) (SLit 4294967295)) B2.
  fact HF (SPUle (SVar 772) (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784)))) C1. fact HF (SPUle (SVar 775) (SAlu ALU_ADD (SVar 425) (SVar 784))) C2.
  fact HF (SPUle (SVar 778) (SAlu ALU_ADD (SVar 428) (SVar 784))) C3. fact HF (SPUle (SVar 781) (SAlu ALU_ADD (SVar 431) (SVar 784))) C4.
  fact HF (SPUle (SVar 422) (SVar 580)) G1. fact HF (SPUle (SVar 425) (SVar 581)) G2. fact HF (SPUle (SVar 428) (SVar 582)) G3. fact HF (SPUle (SVar 431) (SVar 583)) G4.
  fact HF (SPUle (SVar 580) (SMd M_MUL (SLit 3) (SVar 490))) R1. fact HF (SPUle (SVar 581) (SVar 490)) R2. fact HF (SPUle (SVar 582) (SVar 490)) R3. fact HF (SPUle (SVar 583) (SVar 490)) R4.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F8, F9, PA1, B1, B2, C1, C2, C3, C4, G1, G2, G3, G4, R1, R2, R3, R4. rewrite uval_lit in F1, F3, F9, B2 by lia.
  pose proof (uval_range r (SVar 785)) as R785.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 770)) as R770. pose proof (uval_range r (SVar 784)) as R784.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490. pose proof (uval_range r (SVar 14)) as R14.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428. pose proof (uval_range r (SVar 431)) as R431.
  pose proof (uval_range r (SVar 772)) as R772. pose proof (uval_range r (SVar 775)) as R775. pose proof (uval_range r (SVar 778)) as R778. pose proof (uval_range r (SVar 781)) as R781.
  pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 437)) as R437. pose proof (uval_range r (SVar 440)) as R440.
  pose proof (uval_range r (SVar 580)) as R580. pose proof (uval_range r (SVar 581)) as R581. pose proof (uval_range r (SVar 582)) as R582. pose proof (uval_range r (SVar 583)) as R583.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E2 in F6.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 784) (SVar 476)) = uval r (SVar 784) + uval r (SVar 476)) by (apply uval_add_small; lia). rewrite E3 in PA1.
  assert (M3 : uval r (SMd M_MUL (SLit 3) (SVar 490)) = 3 * uval r (SVar 490)) by (apply uval_mul_lit; lia). rewrite M3 in R1.
  assert (M3a : uval r (SMd M_MUL (SLit 3) (SVar 784)) = 3 * uval r (SVar 784)) by (apply uval_mul_lit; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784))) = uval r (SVar 422) + 3 * uval r (SVar 784)) by (rewrite uval_add_small; rewrite M3a; lia). rewrite E4 in C1.
  assert (E5 : uval r (SAlu ALU_ADD (SVar 425) (SVar 784)) = uval r (SVar 425) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E5 in C2.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 428) (SVar 784)) = uval r (SVar 428) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E6 in C3.
  assert (E7 : uval r (SAlu ALU_ADD (SVar 431) (SVar 784)) = uval r (SVar 431) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E7 in C4.
  pose proof (amin1_rng r (SVar 422)) as M1. pose proof (amin1_rng r (SVar 425)) as M2. pose proof (amin1_rng r (SVar 428)) as M3'. pose proof (amin1_rng r (SVar 431)) as M4.
  pose proof (amin1_rng r (SVar 772)) as M5. pose proof (amin1_rng r (SVar 775)) as M6. pose proof (amin1_rng r (SVar 778)) as M7. pose proof (amin1_rng r (SVar 781)) as M8.
  unfold finVf, finKf, LAr_f, LAX, LAK, LAXK, A1, AK1, HF.cVF, pLNL, pPOS, pNX, vLEN. cbv beta iota delta [bsumV bsumK bival lfval bi_v bi_k bi_f bi_c].
  repeat match goal with |- context [aval r (ASv ?e)] => change (aval r (ASv e)) with (uval r e) end. rewrite E2.
  clear HF EX EY. split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval bi_v bi_k bi_f bi_c];
    repeat match goal with |- context [aval r (ASv ?e)] => change (aval r (ASv e)) with (uval r e) end; rewrite ?E2; lia.
Qed.

Lemma rates_f_holds : ltac2:(tb__ "0|0|
S10S2dS12S13R1A1S14S19S4dA1A1A3S2dS12S13R2A1S76A3F_;Fr;").
Proof.
  intros r HF. pose proof af_checks_rt as (_ & _ & EQ & EQA & EQ1 & EQ2 & EQ3 & EQ4).
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 770) (SAlu ALU_ADD (SVar 480) (SVar 481))) F6. fact HF (SPUle (SVar 476) (SVar 770)) F8. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  fact HF (SPUle (SAlu ALU_ADD (SVar 784) (SVar 476)) (SAlu ALU_ADD (SVar 480) (SVar 481))) A0.
  fact HF (SPUle (SVar 784) (SVar 785)) B1. fact HF (SPUle (SVar 785) (SLit 4294967295)) B2.
  fact HF (SPUle (SVar 772) (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784)))) C1. fact HF (SPUle (SVar 775) (SAlu ALU_ADD (SVar 425) (SVar 784))) C2.
  fact HF (SPUle (SVar 778) (SAlu ALU_ADD (SVar 428) (SVar 784))) C3. fact HF (SPUle (SVar 781) (SAlu ALU_ADD (SVar 431) (SVar 784))) C4.
  fact HF (SPUle (SVar 422) (SVar 580)) G1. fact HF (SPUle (SVar 425) (SVar 581)) G2. fact HF (SPUle (SVar 428) (SVar 582)) G3. fact HF (SPUle (SVar 431) (SVar 583)) G4.
  fact HF (SPUle (SVar 580) (SMd M_MUL (SLit 3) (SVar 490))) R1. fact HF (SPUle (SVar 581) (SVar 490)) R2. fact HF (SPUle (SVar 582) (SVar 490)) R3. fact HF (SPUle (SVar 583) (SVar 490)) R4.
  fact HF (SPUle (SVar 587) (SVar 490)) R5. fact HF (SPUle (SVar 588) (SMd M_MUL (SLit 3) (SVar 490))) R6. fact HF (SPUle (SVar 589) (SMd M_MUL (SLit 3) (SVar 490))) R7.
  fact HF (SPUle (SVar 590) (SMd M_MUL (SLit 37) (SVar 490))) R8.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F8, F9, A0, B1, B2, C1, C2, C3, C4, G1, G2, G3, G4, R1, R2, R3, R4, R5, R6, R7, R8. rewrite uval_lit in F1, F3, F9, B2 by lia.
  pose proof (uval_range r (SVar 785)) as R785.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 770)) as R770. pose proof (uval_range r (SVar 784)) as R784.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490. pose proof (uval_range r (SVar 14)) as R14.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428. pose proof (uval_range r (SVar 431)) as R431.
  pose proof (uval_range r (SVar 772)) as R772. pose proof (uval_range r (SVar 775)) as R775. pose proof (uval_range r (SVar 778)) as R778. pose proof (uval_range r (SVar 781)) as R781.
  pose proof (uval_range r (SVar 580)) as R580. pose proof (uval_range r (SVar 581)) as R581. pose proof (uval_range r (SVar 582)) as R582. pose proof (uval_range r (SVar 583)) as R583.
  pose proof (uval_range r (SVar 587)) as R587. pose proof (uval_range r (SVar 588)) as R588. pose proof (uval_range r (SVar 589)) as R589. pose proof (uval_range r (SVar 590)) as R590.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E2 in F6, A0.
  assert (KM : forall k e, 0 <= k <= 64 -> uval r e <= 2 ^ 32 -> uval r (SMd M_MUL (SLit k) e) = k * uval r e) by (intros k e Hk He; pose proof (uval_range r e); apply uval_mul_lit; [lia | nia]).
  rewrite !KM in R1, R6, R7, R8 by lia.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 784) (SVar 476)) = uval r (SVar 784) + uval r (SVar 476)) by (apply uval_add_small; lia). rewrite E3 in A0.
  assert (E4 : uval r (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784))) = uval r (SVar 422) + 3 * uval r (SVar 784)) by (rewrite uval_add_small; rewrite KM by lia; lia). rewrite E4 in C1.
  assert (E5 : uval r (SAlu ALU_ADD (SVar 425) (SVar 784)) = uval r (SVar 425) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E5 in C2.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 428) (SVar 784)) = uval r (SVar 428) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E6 in C3.
  assert (E7 : uval r (SAlu ALU_ADD (SVar 431) (SVar 784)) = uval r (SVar 431) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E7 in C4.
  assert (ES : uval r (SAlu ALU_SUB (SVar 770) (SVar 476)) = uval r (SVar 770) - uval r (SVar 476)) by (apply uval_sub_le; exact F8).
  assert (EE : uval r xE1 = uval r (SVar 480) + uval r (SVar 481) + 1).
  { unfold xE1, pE0, pPOS, pLNL. rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
  assert (GA : forall g k, 0 <= k <= 64 -> uval r g <= 2 ^ 40 -> uval r (SAlu ALU_ADD g (kb k (SVar 784))) = uval r g + k * uval r (SVar 784)).
  { intros g k Hk Hg. pose proof (uval_range r g). unfold kb. rewrite uval_add_small; rewrite KM by lia; nia. }
  assert (GB : forall g, uval r g <= 2 ^ 40 -> uval r (SAlu ALU_ADD g (SVar 784)) = uval r g + uval r (SVar 784)) by (intros g Hg; pose proof (uval_range r g); apply uval_add_small; lia).
  unfold rates_f, gMI', gFV', gMM', gSG', gCO', gRP', gTR', gTS', gMI, gFV, gMM, gSG, gCO, gRP, gTR, gTS. rewrite EQ, EQA, EQ1, EQ2, EQ3, EQ4. unfold pCP.
  repeat (apply Forall_cons; [apply (proj2 (h_ule _ _ _)); unfold kb; rewrite ?KM by (rewrite ?EE; lia); rewrite ?EE; fold (kb 3 (SVar 784)); fold (kb 37 (SVar 784));
                              rewrite ?GA, ?GB by lia; try (rewrite uval_add_small; rewrite ES; [|lia]); lia|]).
  constructor.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S82S10S5S1bQ40A1A1S3fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S6bS2VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S7cVCST;R1A2S29S2bZ0R2A2S2cR2S81A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S7cVXGL;R1A2S29S2bZ0R2A2S2cR2S81A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S0S87R1A1S7cVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S3S3S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF3 : ltac2:(tb__ "0|1|
S2aS6S80Z3S2eS3S3S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3").
Hypothesis HFF6 : ltac2:(tb__ "0|1|
S2aS6S80Z6S2eS3S3S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S10OFr;") := ltac2:(tb__ "0|0|
S88VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S22VAInv;VCST;VXGL;S78VKc;Vrho0;VP0;VFB;VFF;VBX;S20Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S39VAInv;VCST;VXGL;S78VKc;Vrho0;VP0;VFB;VFF;VBX;S20VPhi;Vnd;Ad").

Lemma HIN_f : ltac2:(tb__ "0|1|
S10S48S82S10S5S1bQ40A1A1S3fS2dS12S13R6A1S14S19S4bA1A1A3VP0;Vrho0;A1S7dS78Vrho0;R8A3VAInv;R7R6R5R4A4S23Vrho0;R8A2S8aRbS84S83R9A1A1A2S24VFB;RaA2S25VFF;RbA2S28VFB;RcReSbS3S11S11A2S49S51A3M0A4S8bRfG0A2S8cR10G0A2S26VFF;RfR11S34A4S29S90VCST;Vrho0;VFB;VFF;R12S49S34S4cA8S29S91VCST;VXGL;Vrho0;VFB;VFF;R12S49S34S50A9S36VCST;S89VFB;R12S49A3S8fVFF;R12S34A3S3bS3cR12S4cR11A3S54A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof af_checks2 as (CR & CX & CLN).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_f) by (apply (tvinA_sublist FB Ai rho (kept_f ++ passed_f)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_f) by (exact (tvd_app_l rho kept_f passed_f HD)).
  assert (HZk : tvz rho kept_f) by (apply (tvz_sublist rho (kept_f ++ passed_f)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_f frL extra_f R_f rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_f in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_f frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_f frL o a HF CLN HT0 HZk lines_in_kept_f HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_f frL xextraLO Xk_f rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_f frL r a Hav HP0 HE Ha).
  - pose proof af_checks as (_ & _ & _ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold HFI.P0_hf, P0_builder. rewrite !rw_call'.
    change (wsub_get s_f 15) with vBUF. change (wsub_get s_f 18) with vLEN. change (wsub_get s_f 12) with bA. change (wsub_get s_f 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|split].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_f rho R_f ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho kept_f) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_f) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF3. reflexivity.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF6. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S5S1bQ40A1A1S2fF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1dS18S10S5S1bQ40A1A1S2fS2dS12S13R3A1S14S19R4A1A1A3VTR;S1cS2R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2fS2fS2fS32R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2fOS2fS32R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S1dS1dS18S18S3dS5S17A1M0S5S3S18S59A2M1A1S5S3S11S11A2M2A1S2fS10S5S1bQ40A1A1M3G2S35G2R1R5A3S35G2R2S1aRbA1A3F_;Fr;S2aSeG0A1S5cRaR9R8A3SdG0R7A2A3S2aS9S5bRbRaR9R8S2eG1S18SaS18S59A2R7A4A5S7A3S10G3VTR;S1cS2RfRdR2R1A5S58S2S15S19RdA1A1R2R1RaA5A2Ftp1;Frho1;S5S40A1M4S48S3fS1eS2R9R8R10S4G4S6cR3S6dR2R1A2A4A5R13RaR9R4R2A4R13S3bS3cRbRfS3eR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S18S59G4S48S3fS10G3G4S48S3fS35G1S4S18S59RaR9A4R14A3S1eS2R12R11R19S4G4S6cR9S6dR8R7A2A4A5R1cR13R12RaR8A4S7dS15S19R1aA1A1S3bS3cR14R18S3eR9R13RaA3A3R19A2R8A3S1eS2R9R8ReS4G4S6cR7S6dR6R5A2A4A5ReS3bS3cR16R1aS3eRbR15RcA3A3R1bA2R15RaR9R8R6A6S29S8dR17S3eRcR16RdA3R1bR1cR1dR10R1eR19RbA9S10S7eR18S3eRdR17ReA3R1cR1dS19R1eA1S19R1fA1S19R11A1R1RcA9VTR;S1cS2S5aR11S3bS3cR19R1dS3eReR18RfA3A3R1eA2R18RdRcA5S8eR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1cS2R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S10OF_;S1fS18S10S5S1bQ40A1A1S2fR6R3A1VTR;S1cS2VJAv;R6A1R5R4R3A5R2A2F_;VTR;S1cS2VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHF : ltac2:(tb__ "0|1|
S5S3S0S0A2M0A1S5S3G0S0A2A1S60S10S5S1bQ40A1A1S5eZ6R3A2VTR;S1cS2S21VAInv;VCST;VXGL;VKc;S36VCST;R6R5A3R6R5R4S20S7aS56S7S70A3AaS6fR3R2A5S58S2S6eR3R2S7bVAInv;VCST;VXGL;VKc;S36VCST;A1S20S4aR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
S18S1fS6S3S0S11A2M0S10S5S1bQ40A1A1M1S0G1S35S3S3S3S18S1fA2M2S6A2M3G0A2S4G3G0S4G2S6S4S18S1fR8R7A4R6A4R5A4S73A3S38S55R7R5A3S29S2bZ0S37S4G3G0S4G2S6S4S18S1fRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2VTR;S1cS2VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_f : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0VTR;S1cS2VJAFv;S33S41A2S47R3R2A5VFAM;S37S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS47S41A4U1A4S4S0S11S42S43Z11S45A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof af_checks as (Cxf & CEf & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & Chand & PP1 & PP2 & PWc & PWy & Cnb & Cbr & Cnp & Cnx & _).
  pose proof af_checks2 as (_ & _ & CLN).
  set (ndv := NDA tv_f frL bd_f (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_f rho tp)).
  { intros w Hw. rewrite <- CEf. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_f rho E_hf E_f1 tp w Cxf).
      unfold ndv, tv_f. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_f _ E_hf rho tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hf rho tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [exact (room_f_holds rho HF1) | exact HF1]. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_f HF CLN HTK HZ). unfold tv_f. apply in_or_app. left. exact lines_in_kept_f. }
  intros Hdnz.

  unfold ndv, tv_f.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (HFI.P0_hf CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HF.Pre_hf (ndh h0 true HF.nd0) PDk_f NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHF eq_refl
           E_f s_f R_f Xk_f rho tp kept_f passed_f frL bd_f brest_f (AHead pH true) (FAM (efmeasA (E_hf, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  -
    rewrite Chand. unfold payA.
    apply (pay_okF_split_semF _ _ (SLit 0) 0 bd_f _ payC_f payX_f payY_f PP1 PP2 PWc PWy (Z.le_refl 0)). intros r HFr Hnn. exact (pay_site_f r HFr Hnn).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_f rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_f frL rho' HK lines_in_kept_f Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof af_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & _).
    pose proof af_checks_rt as (RT & Rfb & _).
    cbn [PDk_f liftPD PDh HFI.PD_hf HFE.Posts_hf map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_f_f) T_f_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_f_f) (xfb_f T_f_f0) rho' T_f_f0 B_f_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof af_checks_payf as (QP1 & QP2 & QPay & _ & _).
      apply (TR_pre (SPA segs (JAv nd_f_fX) T_f_f rho' tp')).
      { intros w Hw. unfold nd_f_fX, nd_f_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_f_f frL (AHead pH true) bd_f_f commf_f Xf_f Yf_f bd_f_fX _ T_f_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_f_f nd_f_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hf T_f_f ndA1 nd_f_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_f_ok) T_f_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_f_ok) (xfb_f T_f_ok0) rho' T_f_ok0 B_f_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof af_checks_pay as (PQ1 & PQ2 & PWy' & _).
      apply (TR_pre (SPA segs (JAv nd_f_okX) T_f_okR rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb | intros tr md _ _; apply Forall_app; split; [exact (rates_f_holds rho' HFo) | exact HFo]].
        unfold nd_f_okX, nd_f_ok in *.
        exact (SPA_bd_repay_sem AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_f_ok frL (AHead pH true) bd_f_ok comm_f Xs_f Ys_f bdX_f _ T_f_ok rho' tp' w PQ1 PQ2 PWy' HFo (pay_f rho') Hw). }
      apply (CUTV T_f_okR nd_f_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hf T_f_okR ndA1 nd_f_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Lemma Lok_f_latch : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1S32S33R3A1S1cS2VJAv;S75A1S74R4R3R2A6S29S33S3bR5S77A2M0A1S1cS2VJAv;S44A1S57G0R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof af_checks_exit as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & _ & _ & Xperm).
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lok_f X_latch s_latch_f nd_f_okX tv_f (bdX 0) (AHead pH true) tblB V_B rho tp w
              tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HP HS) as [HP' HS'].
  split; [exact HP'|]. unfold ndX0, ndL. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_f tvL frL (bdX 0) (AHead pH true) X_latch _ tp w Xperm HS').
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S27S2VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S69S2S68VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S0S35S0R1S8S0Z0S8S0Zf5S8S0Zf8ScS0A1A3A3A3A3S85S2S68VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis CHFs : HFI.handle_f_stmt.
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1M0G0S31S2Vok;S1cS2VJAFv;S33S44A2S57R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1M0G0S31S2Vok;S1cS2VJAFv;S33S46A2S79R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHF_T : ltac2:(tb__ "0|1|
S5S3S0S0A2M0A1S5S3G0S0A2A1S60S10S5S1bQ40A1A1S5eZ6R3A2S31S2Vok;S1cS2S21VAInv;VCST;VXGL;VKc;S36VCST;R6R5A3R6R5R4S20S7aS56S7S70A3AaS6fR3R2A5S58S2S6eR3R2S7bVAInv;VCST;VXGL;VKc;S36VCST;A1S20S4aR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_f.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (HFI.P0_hf CST) PTrue HF.Pre_hf (ndh h0 true HF.nd0) (PDh HFI.PD_hf h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (HFI.P0_hf CST) PTrue HF.Pre_hf HF.nd0 HFI.PD_hf NPH h0 true h0_ltH HFI.HamC_hf HFI.HamPD_hf (HFI.P0_hf_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''.
  exact (CHFs AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC SSC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S18S1fS6S3S0S11A2M0S10S5S1bQ40A1A1M1S0G1S35S3S3S3S18S1fA2M2S6A2M3G0A2S4G3G0S4G2S6S4S18S1fR8R7A4R6A4R5A4S73A3S38S55R7R5A3S29S2bZ0S37S4G3G0S4G2S6S4S18S1fRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S31S2Vok;S1cS2VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsQ) (map efdrop exitsQ) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertQ_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1) ok). intros HP1.
    eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho1 s_latch_f) tp1 tp0')].
    intros w Hw. destruct (Lok_f_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_f tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 af_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_f_T : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1M0G0S31S2Vok;S1cS2VJAFv;S33S41A2S47R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_f (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHF_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6aS2S68VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S0S35S0R1S8S0Z0S8S0Zf5S8S0Zf8ScS0A1A3A3A3A3S86S2S68VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis CHFx : HFI.handle_f_stmt_ex.
Variable FAM : ltac2:(tb__ "0|0|
S0S5S1bQ40A1A1S2fF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S0S0S5S1bQ40A1A1S32S2bR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0S30S2S1cS2VJAFv;S33S44A2S57R3R2A5VFAM;S37S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS57S44A4U1A4S4S0S11S42S43Z1S45A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0S30S2S1cS2VJAFv;S33S46A2S79R3R2A5VFAM;S37S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS79S46A4U1A4S4S0S11S42S43Z1S45A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHF_E : ltac2:(tb__ "0|1|
S5S3S0S0A2M0A1S5S3G0S0A2A1S60S10S5S1bQ40A1A1S5eZ6R3A2S30S2S1cS2S21VAInv;VCST;VXGL;VKc;S36VCST;R6R5A3R6R5R4S20S7aS56S7S70A3AaS6fR3R2A5S58S2S6eR3R2S7bVAInv;VCST;VXGL;VKc;S36VCST;A1S20S4aR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_f.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (HFI.P0_hf CST) PTrue HF.Pre_hf (ndh h0 true HF.nd0) (PDh HFI.PD_hf h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (HFI.P0_hf CST) PTrue HF.Pre_hf HF.nd0 HFI.PD_hf NPH h0 true h0_ltH HFI.HamC_hf HFI.HamPD_hf (HFI.P0_hf_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''.
  exact (CHFx AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX SSCX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S18S1fS6S3S0S11A2M0S10S5S1bQ40A1A1M1S0G1S35S3S3S3S18S1fA2M2S6A2M3G0A2S4G3G0S4G2S6S4S18S1fR8R7A4R6A4R5A4S73A3S38S55R7R5A3S29S2bZ0S37S4G3G0S4G2S6S4S18S1fRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S30S2S1cS2VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsQ exitsQ (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertQ_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    eapply etriple_conseq; [| intros w Hw; right; exact Hw |].
    2: { pose proof af_checks_exit as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
         rewrite <- (efmeasA_VLA_sub X_latch Lok_f ndX0 nd_f_okX 1%nat 1%nat RL 1 s_latch_f rho1 W460 W467).
         exact (XLATCH (rho_sub rho1 s_latch_f) tp1 tp0'). }
    intros w Hw. destruct (Lok_f_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_f tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 af_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_f_E : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0S30S2S1cS2VJAFv;S33S41A2S47R3R2A5VFAM;S37S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS47S41A4U1A4S4S0S11S42S43Z11S45A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_f (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHF_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
