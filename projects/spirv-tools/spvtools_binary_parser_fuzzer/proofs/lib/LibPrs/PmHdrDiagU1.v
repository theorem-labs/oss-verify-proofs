(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HFpu HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1 PmLoopU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation d1_stmt := (PmLoopU1.d1_stmt (MI:=MI) (ST:=ST)).

  Lemma ro_11728 : ro_cstr SEGS Ly.L 0x11728 15.
  Proof using. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.

  Lemma pm_D1 : forall (w : pmw MI ST) c0 K (fx : FPState),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> d1_stmt w c0 K fx.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx PS FZ A M model c R X Htr BUD Hw0 Qs0 Qa0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
    { split_scs; try sc_auto1. }
    postrun. name_run HR1 R1.
    rreg HR1 (1%bv) G1. rreg HR1 (2%bv) G2. rreg HR1 (3%bv) G3. rreg HR1 (4%bv) G4. rreg HR1 (8%bv) G8.
    rreg HR1 (10%bv) G10. rreg HR1 (11%bv) G11. rreg HR1 (12%bv) G12.
    rewrite w_add in G10 by lia. clear HR1 HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | rewrite Zlength_nil; lia | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11
      | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    intros A' R2 M' model' B' X' BUD' KEPT DS' AG.
    pose proof (x_ms X') as MS'.
    keptQ KEPT G8 Q8'. keptQ KEPT G2 Q2'. keptQ KEPT G3 Q3'. keptQ KEPT G4 Q4'.
    clear G1 G2 G3 G4 G8 G10 G11 G12.
    pm_seed R2 w (set_tr c (B' ++ [])) (@nil word). seedHR HR2 E [(2%bv, EVar 32); (8%bv, EVar 33)] R2. seedHK HK2 w A' M' model' (set_tr c (B' ++ [])) E X'.
    xruns HR2 HK2 100%nat STOPS (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1. }
    name_run HR3 R3.
    rreg HR3 (1%bv) G1. rreg HR3 (2%bv) G2. rreg HR3 (3%bv) G3. rreg HR3 (4%bv) G4.
    rreg HR3 (10%bv) G10. rreg HR3 (11%bv) G11. rreg HR3 (12%bv) G12. rewrite w_add in G10 by lia.
    clear HR3 HR2 HK2. fixregs. rewrite Q3' in G3. rewrite Q4' in G4.
    eapply (pm_put_cstr w c0 K fx A' M' model' (set_tr c (B' ++ [])) R3 (-4) _ 0x11728 15 15 _ B' []);
      [exact PS | exact X' | reflexivity | exact BUD' | rewrite Zlength_nil; lia | exact DS' | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ro_11728 | lia | unfold DS_MAXLEN; lia |].
    intros A2 R4 M2 model2 B2 X2 BUD2 KEPT2 _ DS2 AG2.
    eapply (pm_tail_6733c w c0 K fx A2 M2 model2 _ R4 (-4) _ B2);
      [exact PS | exact X2 | cbn [c_tr set_tr]; apply app_nil_r | exact BUD2 | exact DS2 | lia | exact FZ
      | rewrite (KEPT2 2%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]); exact G2
      | rewrite (KEPT2 3%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]); exact G3
      | rewrite (KEPT2 4%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]); exact G4].
  Qed.

  Lemma pm_D2 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_n w <= 4 ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x6726c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD Hn4 FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | rewrite Zlength_nil; lia | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11
      | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10be0 35 35 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | rewrite Zlength_nil; lia | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u64 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (w_n w) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-4) _ 0x12196 18 18 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | rewrite Zlength_nil; lia | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R5 (-4) _ (5) _ B4 []);
      [exact PS | exact X4 | reflexivity | exact BUD4 | rewrite Zlength_nil; lia | exact DS4 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; f_equal; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat (0x673e0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_tail_6733c w c0 K fx A5 M5 model5 _ R6 (-4) _ B5);
      [exact PS | exact X5 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD5 | exact DS5 | lia | exact FZ
      | exact G2 | exact G3 | exact G4].
  Qed.

  Lemma pm_D4 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x673bc M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-1) _ []);
      [exact PS | exact X | exact Htr | exact BUD | rewrite Zlength_nil; lia | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11
      | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-1) _ 0x126ba 46 46 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | rewrite Zlength_nil; lia | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    eapply (pm_tail_6733c w c0 K fx A2 M2 model2 _ R2c (-1) _ B2);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | exact DS2 | lia | exact FZ
      | exact Qsp | exact Qgp | exact Qtp].
  Qed.

  Lemma pm_D3 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_words w <> 0 -> 1 <= w_n w ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x67300 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD Hw Hn FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia. rewrite ?w_add in G9 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | rewrite Zlength_nil; lia | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11
      | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT G9 Qs1.
    clear G1 G2 G3 G4 G8 G9 KEPT AG; try clear G10; try clear G11; try clear G12.
    pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite Qs1 in G9.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x11f5e 29 29 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | rewrite Zlength_nil; lia | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. clear Qs1. keptQ KEPT G9 Qs1.
    clear G1 G2 G3 G4 G8 G9 KEPT AG; try clear G10; try clear G11; try clear G12.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.

    destruct (dl_hex _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as (vt & fl & Hvt & Hvb & Rvt & Rfl & Vb0 & Vb1 & Hfl & HEX). unfold DS_FL0, DS_FLHEX in Rfl.
    unshelve epose proof (Hvb M2 _ (ex_intro _ (w_s w) (x_sx X2))) as Hvb'; [eapply pmx_img_ro_clear; exact X2|]. cbn [dc_vboff dcU1] in Hvb', Hfl, HEX.
    replace (vt - 24) with (vt + -24) in Hvb' by lia.
    destruct (mdef_cell4 M2 (w_words w) ltac:(eapply mdef_sub; [exact (x_wbuf X2 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (v0 & Cv0).
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 vt; Z_to_bv 64 fl; Z_to_bv 64 v0; sxw v0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 304))] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 304) (N.to_nat 8) (EVar 39); KWord (SA (EVar 39) (-24)) (N.to_nat 8) (ELit 112);
                              KWord (SA (EVar 32) 424) (N.to_nat 4) (EVar 40); KWord (SA (EVar 34) 0) (N.to_nat 4) (EVar 41);
                              KDisj (SA (EVar 34) 0) (ELit 4) (SA (EVar 32) 0) (ELit 864); KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 4]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact Hvt | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact Hvb' | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [replace (w_sp w + 424) with (w_sp w + 304 + 112 + 8) by lia; exact Hfl | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [replace (w_words w + 0) with (w_words w) by lia; exact Cv0 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia |].
           destruct (Z.lt_ge_cases (w_words w + 0 + 4) (w_sp w + 0 + 1)) as [?|Hge]; [left; lia | right].
           destruct (W5 (w_words w) ltac:(unfold zwin; lia)) as [Hnw _]. unfold zwin in Hnw. lia.
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite ?w_add in G10 by lia. clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite ext_val_sx4 in G11 by (destruct Cv0 as [Rv0 _]; cbn in Rv0; lia).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ (wbytes _ _ (word_to_le_bytes 4 ?fw)) _) _) _ => set (FW := fw) end.
    assert (EW : word_to_le_bytes 4 FW = word_to_le_bytes 4 (Z_to_bv 64 DS_FLHEX)) by (unfold FW; destruct Rfl as [-> | ->]; vm_compute; reflexivity).
    rewrite EW. clear EW FW.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mh := m) end.
    assert (STh : stores_in (zwin (w_sp w + 424) (w_sp w + 428)) M2 Mh) by (unfold Mh; stin).
    assert (Xh : PMX w A2 Mh model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ []))).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X2 | exact STh | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eassert (DSh : ds_rep A2 Mh (w_sp w + 304) (-4) _ B2).
    { unfold Mh. replace (w_sp w + 424) with (w_sp w + 304 + 112 + 8) by lia. exact HEX. }
    clear STh X2 DS2 HEX Hvt Hvb Hvb' Hfl. clearbody Mh. rename Xh into X2. rename DSh into DS2. destruct Cv0 as [Rv0 _]. cbn in Rv0.
    eapply (pm_put_u32 w c0 K fx A2 Mh model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R9 (-4) _ (v0) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-4) _ 0x11095 2 2 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | rewrite Zlength_nil; lia | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G10; try clear G11; try clear G12.
    try clear X3 BUD3 DS3.
    eapply (pm_tail_6733c w c0 K fx A4 M4 model4 _ R4c (-4) _ B4);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | exact DS4 | lia | exact FZ
      | exact Qsp | exact Qgp | exact Qtp].
  Qed.
End PM.
