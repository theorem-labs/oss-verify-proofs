(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_pf"; "P0_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al"; "kept_l"; "PDk_l"; "R_l"; "T_l_ok"; "E_l"; "Xk_l"; "passed_l"; "rates_l"; "s_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al.HL"; "Pre_hl"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al_eqs"; "Xs_l"; "Ys_l"; "cutsQ"; "Lok_l"; "nd_l_okX"; "s_latch_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "bd_nn"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al.HL2"; "Posts_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_al Lib_load_obj_al_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HLAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S35S1S3SdA1M0S11OF_;M1A2M2G2S3aS6G0G1R1A3S7G0G1R1A3A2Lp;S52A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_l : nd_am HL.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_l : ltac2:(tb__ "0|1|
S35S1SeS18A2M0G0S2aS1eS22S7SeS18R1A3A1S1bA3Ld;S7aA3"). Proof. repeat constructor. Qed.
Lemma P0_hl_mono : ltac2:(tb__ "0|2|
S3S1ScScA2M0A1M1G1G1S3S1G0ScA2A1S11G0S32G0R1R5A3S32G0R2R5A3F_;Fbn;S2fR6R5R3R2A4S2fR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & E). split; [|exact E]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma pay_l : ltac2:(tb__ "0|0|
S11S35S14S13R1A1S15SfS4cA1A1A3S69S5fR2A2S29S33S6bS60R3A2S6bS5fR3A2A2S29S33S6aS60R3A2S6aS5fR3A2A2S69S60R3A2A2A2F_;F_;Fr;").
Proof.
  intros r HF _. pose proof al_checks_pay as (_ & _ & _ & EX & EY & EQ & _). rewrite EX, EY. rewrite EQ.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 480) (SVar 481))) F6. fact HF (SPUle (SAlu ALU_ADD (SVar 762) (SVar 476)) (SAlu ALU_ADD (SVar 434) (SVar 760))) F7.
  fact HF (SPUle (SVar 434) (SLit 4294967295)) F8. fact HF (SPUle (SVar 762) (SVar 763)) F9. fact HF (SPUle (SVar 763) (SLit 4294967295)) F10.
  fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 480) (SVar 481))) F11.
  fact HF (SPUle (SVar 767) (SAlu ALU_ADD (SVar 437) (SLit 1))) F13. fact HF (SPUle (SVar 437) (SVar 585)) F14.
  fact HF (SPUle (SVar 585) (SAlu ALU_ADD (SAlu ALU_ADD (SVar 480) (SVar 481)) (SLit 1))) F15.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F13, F14, F15. rewrite uval_lit in F1, F3, F8, F10 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 762)) as R762. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428.
  pose proof (uval_range r (SVar 431)) as R431. pose proof (uval_range r (SVar 440)) as R440. pose proof (uval_range r (SVar 437)) as R437.
  pose proof (uval_range r (SVar 767)) as R767. pose proof (uval_range r (SVar 585)) as R585.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F12. rewrite h_ule, uval_lit in F12 by lia.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  rewrite E2 in F6, F11.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 762) (SVar 476)) = uval r (SVar 762) + uval r (SVar 476)) by (apply uval_add_small; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 434) (SVar 760)) = uval r (SVar 434) + uval r (SVar 760)) by (apply uval_add_small; lia).
  rewrite E3, E4 in F7.
  assert (E5 : uval r (SAlu ALU_ADD (SAlu ALU_ADD (SVar 480) (SVar 481)) (SLit 1)) = uval r (SVar 480) + uval r (SVar 481) + 1) by (rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia); rewrite E1, uval_lit by lia; lia).
  rewrite E5 in F15.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 437) (SLit 1)) = uval r (SVar 437) + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite E6 in F13.
  unfold LAr, LAX, LAK, LAXK, A1, AK1, pLNL, pPOS, pNX, vLEN. cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite E2.
  split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?E2; lia.
Qed.

Lemma rates_l_holds : ltac2:(tb__ "0|0|
S11S35S14S13R1A1S15SfS4cA1A1A3S35S14S13R2A1S50A3F_;Fr;").
Proof.
  intros r HF. pose proof al_checks_pay as (_ & _ & _ & _ & _ & EQ & EQ1 & EQ2 & _).
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 480) (SVar 481))) F6. fact HF (SPUle (SVar 584) (SVar 490)) F7. fact HF (SPUle (SVar 476) (SVar 760)) F8.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F9. fact HF (SPUle (SVar 585) (SVar 490)) F10.
  fact HF (SPUle (SAlu ALU_ADD (SVar 762) (SVar 476)) (SAlu ALU_ADD (SVar 434) (SVar 760))) F11. fact HF (SPUle (SVar 434) (SVar 584)) F12.
  fact HF (SPUle (SVar 767) (SAlu ALU_ADD (SVar 437) (SLit 1))) F13. fact HF (SPUle (SVar 437) (SVar 585)) F14.
  fact HF (SPUle (SVar 434) (SLit 4294967295)) F15. fact HF (SPUle (SVar 762) (SVar 763)) F16. fact HF (SPUle (SVar 763) (SLit 4294967295)) F17.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17. rewrite uval_lit in F1, F3, F9, F15, F17 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 584)) as R584. pose proof (uval_range r (SVar 585)) as R585. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 762)) as R762. pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 767)) as R767. pose proof (uval_range r (SVar 437)) as R437.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E2 in F6.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 762) (SVar 476)) = uval r (SVar 762) + uval r (SVar 476)) by (apply uval_add_small; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 434) (SVar 760)) = uval r (SVar 434) + uval r (SVar 760)) by (apply uval_add_small; lia).
  rewrite E3, E4 in F11.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 437) (SLit 1)) = uval r (SVar 437) + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite E6 in F13.
  assert (ES : uval r (SAlu ALU_SUB qCURl pCP) = uval r (SVar 760) - uval r (SVar 476)) by (rewrite EQ; unfold pCP; apply uval_sub_le; exact F8).
  assert (EG1 : uval r gLI' = uval r (SVar 584) + (uval r (SVar 760) - uval r (SVar 476))) by (unfold gLI', gLI; rewrite <- ES; apply uval_add_small; rewrite ES; lia).
  assert (EG2 : uval r gLC' = uval r (SVar 585) + 1) by (unfold gLC', gLC; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (EE : uval r (SAlu ALU_ADD pE0 (SLit 1)) = uval r (SVar 480) + uval r (SVar 481) + 1).
  { unfold pE0, pPOS, pLNL. rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
  unfold rates_l, rate_gli, rate_glc, cg_li, cg_lc. rewrite EQ1, EQ2.
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG1, EE; lia|].
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG2, EE; lia|].
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG1; lia|].
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG2; lia|]. constructor.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S76S11S3S25Q40A1A1S3fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S75S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
ScS6eVCST;R1A2S29S33Z0R2A2S34R2S71A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
ScS6eVXGL;R1A2S29S33Z0R2A2S34R2S71A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
ScS79R1A1S6eVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1ScScA2ScA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF1 : ltac2:(tb__ "0|1|
S2aS4S85Z1S36S1S1ScScA2M0ScA2G0S6G0ScA2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S7bVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1cVAInv;VCST;VXGL;S65VKc;Vrho0;VP0;VFB;VFF;VBX;S19Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S39VAInv;VCST;VXGL;S65VKc;Vrho0;VP0;VFB;VFF;VBX;S19VPhi;Vnd;Ad").

Lemma HIN_l : ltac2:(tb__ "0|1|
S11S48S76S11S3S25Q40A1A1S3fS35S14S13R6A1S15SfS4dA1A1A3VP0;Vrho0;A1S6fS65Vrho0;R8A3VAInv;R7R6R5R4A4S1dVrho0;R8A2S7dRbS78S77R9A1A1A2S1fVFB;RaA2S20VFF;RbA2S24VFB;RcReS9S1S12S12A2S49S4fA3M0A4S7eRfG0A2S7fR10G0A2S21VFF;RfR11S31A4S29S83VCST;Vrho0;VFB;VFF;R12S49S31S4bA8S29S84VCST;VXGL;Vrho0;VFB;VFF;R12S49S31S4eA9S2fVCST;S7cVFB;R12S49A3S82VFF;R12S31A3S3bS3cR12S4bR11A3S51A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof al_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_l) by (apply (tvinA_sublist FB Ai rho (kept_l ++ passed_l)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_l) by (exact (tvd_app_l rho kept_l passed_l HD)).
  assert (HZk : tvz rho kept_l) by (apply (tvz_sublist rho (kept_l ++ passed_l)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_l frL extra_l R_l rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_l in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_l frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_l frL o a HF CLN HT0 HZk lines_in_kept_l HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_l frL xextraLO Xk_l rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_l frL r a Hav HP0 HE Ha).
  - pose proof al_checks as (_ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_hl, P0_builder. rewrite !rw_call'.
    change (wsub_get s_l 15) with vBUF. change (wsub_get s_l 18) with vLEN. change (wsub_get s_l 12) with bA. change (wsub_get s_l 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 448) = 448) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 368) = 368) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 448) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 368) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_l rho R_l ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0 (FBx FB rho kept_l) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_l) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF1. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
ScS3S25Q40A1A1S2bF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S27SeS11S3S25Q40A1A1S2bS35S14S13R3A1S15SfR4A1A1A3VTR;S26S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2bS2bS2bS2eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2bOS2bS2eR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S27S27SeSeS3dS3S17A1M0S3S1SeS56A2M1A1S3S1S12S12A2M2A1S2bS11S3S25Q40A1A1M3G2S32G2R1R5A3S32G2R2S10RbA1A3F_;Fr;S2aSbG0A1S59RaR9R8A3S8G0R7A2A3S2aSaS58RbRaR9R8S36G1SeS6SeS56A2R7A4A5S5A3S11G3VTR;S26S0RfRdR2R1A5S55S0S16SfRdA1A1R2R1RaA5A2Ftp1;Frho1;S3S40A1M4S48S3fS28S0R9R8R10S2G4S5aR3S5bR2R1A2A4A5R13RaR9R4R2A4R13S3bS3cRbRfS3eR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SeS56G4S48S3fS11G3G4S48S3fS32G1S2SeS56RaR9A4R14A3S28S0R12R11R19S2G4S5aR9S5bR8R7A2A4A5R1cR13R12RaR8A4S6fS16SfR1aA1A1S3bS3cR14R18S3eR9R13RaA3A3R19A2R8A3S28S0R9R8ReS2G4S5aR7S5bR6R5A2A4A5ReS3bS3cR16R1aS3eRbR15RcA3A3R1bA2R15RaR9R8R6A6S29S80R17S3eRcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S70R18S3eRdR17ReA3R1cR1dSfR1eA1SfR1fA1SfR11A1R1RcA9VTR;S26S0S57R11S3bS3cR19R1dS3eReR18RfA3A3R1eA2R18RdRcA5S81R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S26S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S18SeS11S3S25Q40A1A1S2bR6R3A1VTR;S26S0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S26S0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHL : ltac2:(tb__ "0|1|
S3S1ScScA2M0A1S3S1G0ScA2A1S68S11S3S25Q40A1A1S67Z5R3A2VTR;S26S0S1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S6cS53S5S5eA3AaS5dR3R2A5S55S0S5cR3R2S6dVAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4aR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
SeS18S4S1ScS12A2M0S11S3S25Q40A1A1M1ScG1S32S1S1S1SeS18A2M2S4A2M3G0A2S2G3G0S2G2S4S2SeS18R8R7A4R6A4R5A4S61A3S38S52R7R5A3S29S33Z0S37S2G3G0S2G2S4S2SeS18RaR9A4R8A4R7A4R6A2M4A2S34G4R4A2A2VTR;S26S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_l : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0VTR;S26S0VJAFv;S30S41A2S47R3R2A5VFAM;S37S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S47S41A4U1A4S2ScS12S42S43Z11S45A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof al_checks as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnx).
  pose proof al_checks2 as (_ & _ & CLN & _).
  set (ndv := NDA tv_l frL bd_l (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_l rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) xf_l rho E_hl E_l tp w Cxf).
    unfold ndv, tv_l. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_l _ E_hl rho tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hl rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_l HF CLN HTK HZ). unfold tv_l. apply in_or_app. left. exact lines_in_kept_l. }
  intros Hdnz.

  unfold ndv, tv_l.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_hl CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HL.Pre_hl (ndh h0 true HL.nd0) PDk_l NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHL eq_refl
           E_l s_l R_l Xk_l rho tp kept_l passed_l frL bd_l brest_l (AHead pH true) (FAM (efmeasA (E_hl, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  -
    unfold payA. apply (pay_okF_split _ _ _ _ bd_l _ payC_l payX_l payY_l PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_l rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_l frL rho' HK lines_in_kept_l Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof al_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & RT & Rfb).
    cbn [PDk_l liftPD PDh HL2.Posts_hl map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_l_f) T_l_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_l_f) (xfb_l T_l_f0) rho' T_l_f0 B_l_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof al_checks_payf as (QP1 & QP2 & QPay & _ & _).
      apply (TR_pre (SPA segs (JAv nd_l_fX) T_l_f rho' tp')).
      { intros w Hw. unfold nd_l_fX, nd_l_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_l_f frL (AHead pH true) bd_l_f commf_l Xf_l Yf_l bd_l_fX _ T_l_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_l_f nd_l_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hl T_l_f ndA1 nd_l_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_l_ok) T_l_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_l_ok) (xfb_l T_l_ok0) rho' T_l_ok0 B_l_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof al_checks_pay as (PQ1 & PQ2 & PWy & _).

      apply (TR_pre (SPA segs (JAv nd_l_okX) T_l_okR rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb | intros tr md _ _; apply Forall_app; split; [exact (rates_l_holds rho' HFo) | exact HFo]].
        unfold nd_l_okX, nd_l_ok in *.
        exact (SPA_bd_repay_sem AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_l_ok frL (AHead pH true) bd_l_ok comm_l Xs_l Ys_l bdX_l _ T_l_ok rho' tp' w PQ1 PQ2 PWy HFo (pay_l rho') Hw). }
      apply (CUTV T_l_okR nd_l_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hl T_l_okR ndA1 nd_l_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Lemma Lok_l_latch : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1S2eS30R3A1S26S0VJAv;S63A1S62R4R3R2A6S29S30S3bR5S64A2M0A1S26S0VJAv;S44A1S54G0R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof al_checks_exit as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & _ & _ & Xperm).
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lok_l X_latch s_latch_l nd_l_okX tv_l (bdX 0) (AHead pH true) tblB V_B rho tp w
              tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HP HS) as [HP' HS'].
  split; [exact HP'|]. unfold ndX0, ndL. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_l tvL frL (bdX 0) (AHead pH true) X_latch _ tp w Xperm HS').
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S23S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S73S0S72VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1M0G0S2dS0Vok;S26S0VJAFv;S30S44A2S54R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1M0G0S2dS0Vok;S26S0VJAFv;S30S46A2S66R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHL_T : ltac2:(tb__ "0|1|
S3S1ScScA2M0A1S3S1G0ScA2A1S68S11S3S25Q40A1A1S67Z5R3A2S2dS0Vok;S26S0S1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S6cS53S5S5eA3AaS5dR3R2A5S55S0S5cR3R2S6dVAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4aR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_l.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_hl CST) PTrue HL.Pre_hl (ndh h0 true HL.nd0) (PDh HL2.Posts_hl h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_hl CST) PTrue HL.Pre_hl HL.nd0 HL2.Posts_hl NPH h0 true h0_ltH HamC_l HamPD_l (P0_hl_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_l_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SeS18S4S1ScS12A2M0S11S3S25Q40A1A1M1ScG1S32S1S1S1SeS18A2M2S4A2M3G0A2S2G3G0S2G2S4S2SeS18R8R7A4R6A4R5A4S61A3S38S52R7R5A3S29S33Z0S37S2G3G0S2G2S4S2SeS18RaR9A4R8A4R7A4R6A2M4A2S34G4R4A2A2S2dS0Vok;S26S0VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsQ) (map efdrop exitsQ) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertQ_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1) ok). intros HP1.
    eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho1 s_latch_l) tp1 tp0')].
    intros w Hw. destruct (Lok_l_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_l tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 al_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_l_T : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1M0G0S2dS0Vok;S26S0VJAFv;S30S41A2S47R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_l (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHL_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S74S0S72VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
ScS3S25Q40A1A1S2bF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
ScScS3S25Q40A1A1S2eS33R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0S2cS0S26S0VJAFv;S30S44A2S54R3R2A5VFAM;S37S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S54S44A4U1A4S2ScS12S42S43Z1S45A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0S2cS0S26S0VJAFv;S30S46A2S66R3R2A5VFAM;S37S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S66S46A4U1A4S2ScS12S42S43Z1S45A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHL_E : ltac2:(tb__ "0|1|
S3S1ScScA2M0A1S3S1G0ScA2A1S68S11S3S25Q40A1A1S67Z5R3A2S2cS0S26S0S1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S6cS53S5S5eA3AaS5dR3R2A5S55S0S5cR3R2S6dVAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4aR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_l.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_hl CST) PTrue HL.Pre_hl (ndh h0 true HL.nd0) (PDh HL2.Posts_hl h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_hl CST) PTrue HL.Pre_hl HL.nd0 HL2.Posts_hl NPH h0 true h0_ltH HamC_l HamPD_l (P0_hl_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_l_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SeS18S4S1ScS12A2M0S11S3S25Q40A1A1M1ScG1S32S1S1S1SeS18A2M2S4A2M3G0A2S2G3G0S2G2S4S2SeS18R8R7A4R6A4R5A4S61A3S38S52R7R5A3S29S33Z0S37S2G3G0S2G2S4S2SeS18RaR9A4R8A4R7A4R6A2M4A2S34G4R4A2A2S2cS0S26S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsQ exitsQ (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertQ_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    eapply etriple_conseq; [| intros w Hw; right; exact Hw |].
    2: { pose proof al_checks_exit as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
         rewrite <- (efmeasA_VLA_sub X_latch Lok_l ndX0 nd_l_okX 1%nat 1%nat RL 1 s_latch_l rho1 W460 W467).
         exact (XLATCH (rho_sub rho1 s_latch_l) tp1 tp0'). }
    intros w Hw. destruct (Lok_l_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_l tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 al_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_l_E : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0S2cS0S26S0VJAFv;S30S41A2S47R3R2A5VFAM;S37S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S47S41A4U1A4S2ScS12S42S43Z11S45A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_l (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHL_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
