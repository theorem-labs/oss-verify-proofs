(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmHdrDiagS1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepS1.pmx_ds_room CL).
  #[local] Notation pm_tail_68410 := (PmStepS1.pm_tail_68410 CL).
  #[local] Notation cregs_kept := (PmStepS1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepS1.pm_put_cstr CL).
  #[local] Notation pm_put_num := (PmStepS1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepS1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepS1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepS1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepS1.pm_put_int CL).
  #[local] Notation pm_ctor := (PmStepS1.pm_ctor CL).
  #[local] Notation pm_pdiag := (PmStepS1.pm_pdiag CL).
  #[local] Notation pm_pdiag0 := (PmStepS1.pm_pdiag0 CL).
  #[local] Notation pm_pdiagE := (PmStepS1.pm_pdiagE CL).
  #[local] Notation pm_dtor := (PmStepS1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepS1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepS1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepS1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepS1.pm_binend CL).

  Lemma ro_11728 : ro_cstr SEGS Ly.L 0x11728 15.
  Proof using. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.

  Lemma pm_D1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_words w = 0 ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x66854 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD Hw0 FZ Qs0 Qa0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
    { split_scs; try sc_auto1. }
    postrun. name_run HR1 R1.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
    assert (ST1 : stores_in (zwin (w_sp w) (w_sp w + 776)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    rreg HR1 (1%bv) G1. rreg HR1 (2%bv) G2. rreg HR1 (3%bv) G3. rreg HR1 (4%bv) G4. rreg HR1 (8%bv) G8.
    rreg HR1 (10%bv) G10. rreg HR1 (11%bv) G11. rreg HR1 (12%bv) G12. rreg HR1 (13%bv) G13. rreg HR1 (14%bv) G14. rreg HR1 (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia. clear HR1 HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_ctor w c0 K fx A M1 model c R1 (-4) (w_sp w + 224) (w_sp w + 160) (w_sp w + 752) _ []);
      [exact PS | exact X1 | exact Htr | exact BUD | rewrite Zlength_nil; lia | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold M1; rdback | unfold M1; rdback |].
    intros A' R2 M' model' B' X' BUD' KEPT DS' AG.

    assert (C752 : cellw SEGS M' (w_sp w + 752) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS M1 M' (w_sp w + 752) 1); [unfold M1; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C160 : cellw SEGS M' (w_sp w + 160) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS M1 M' (w_sp w + 160) 1); [unfold M1; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    pose proof (x_ms X') as MS'.
    keptQ KEPT G8 Q8'. keptQ KEPT G2 Q2'. keptQ KEPT G3 Q3'. keptQ KEPT G4 Q4'.
    clear G1 G2 G3 G4 G8 G10 G11 G12 G13 G14 G15.
    pm_seed R2 w (set_tr c (B' ++ [])) [Z_to_bv 64 0]. seedHR HR2 E [(2%bv, EVar 32); (8%bv, EVar 33)] R2. seedHK HK2 w A' M' model' (set_tr c (B' ++ [])) E X'.
    apply (know_more E M' [KWord (SA (EVar 32) 752) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 160) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0]) in HK2.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C752 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C160 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR2 HK2 100%nat STOPS (SCR [true; true] [] []) 50%N.
    { split_scs; try sc_auto1. }
    name_run HR3 R3.
    rreg HR3 (1%bv) G1. rreg HR3 (2%bv) G2. rreg HR3 (3%bv) G3. rreg HR3 (4%bv) G4.
    rreg HR3 (10%bv) G10. rreg HR3 (11%bv) G11. rreg HR3 (12%bv) G12. rewrite w_add in G10 by lia.
    clear HR3 HR2 HK2. fixregs. rewrite Q3' in G3. rewrite Q4' in G4.
    eapply (pm_put_cstr w c0 K fx A' M' model' (set_tr c (B' ++ [])) R3 (-4) _ 0x11728 15 15 _ B' []);
      [exact PS | exact X' | reflexivity | exact BUD' | rewrite Zlength_nil; lia | exact DS' | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ro_11728 | lia | unfold DS_MAXLEN; lia |].
    intros A2 R4 M2 model2 B2 X2 BUD2 KEPT2 _ DS2 AG2.
    eapply (pm_tail_68410 w c0 K fx A2 M2 model2 _ R4 (-4) _ B2);
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
    srealizes SEGS (cfg fx R 0x66868 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD Hn4 FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (zwin (w_sp w) (w_sp w + 776)) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-4) (w_sp w + 224) (w_sp w + 160) (w_sp w + 752) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C752 : cellw SEGS M1 (w_sp w + 752) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 752) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C160 : cellw SEGS M1 (w_sp w + 160) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 160) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 752) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 160) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C752 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C160 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear C752 C160.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10be0 35 35 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u64 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (w_n w) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-4) _ 0x12196 18 18 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R5 (-4) _ (5) _ B4 []);
      [exact PS | exact X4 | reflexivity | exact BUD4 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS4 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; f_equal; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat (0x684b4 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_tail_68410 w c0 K fx A5 M5 model5 _ R6 (-4) _ B5);
      [exact PS | exact X5 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD5 | exact DS5 | lia | exact FZ
      | exact G2 | exact G3 | exact G4].
  Qed.

  Lemma pm_D3 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_words w <> 0 -> 1 <= w_n w ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x669b0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD Hw Hn FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (zwin (w_sp w) (w_sp w + 776)) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-4) (w_sp w + 224) (w_sp w + 160) (w_sp w + 752) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C752 : cellw SEGS M1 (w_sp w + 752) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 752) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C160 : cellw SEGS M1 (w_sp w + 160) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 160) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 752) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 160) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C752 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C160 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear C752 C160.
    rewrite w_add in G9 by lia.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x11f5e 29 29 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. try clear Qs1. keptQ KEPT G9 Qs1.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.

    destruct (dl_hex _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as (vt & fl & Hvt & Hvb & Rvt & Rfl & Vb0 & Vb1 & Hfl & HEX). unfold DS_FL0, DS_FLHEX in Rfl.
    unshelve epose proof (Hvb M2 _ (ex_intro _ (w_s w) (x_sx X2))) as Hvb'; [eapply pmx_img_ro_clear; exact X2|]. cbn [dc_vboff dcS1] in Hvb', Hfl, HEX.
    replace (vt - 24) with (vt + -24) in Hvb' by lia.
    destruct (mdef_cell4 M2 (w_words w) ltac:(eapply mdef_sub; [exact (x_wbuf X2 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (v0 & Cv0).
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 vt; Z_to_bv 64 fl; Z_to_bv 64 v0; sxw v0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 272))] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 272) (N.to_nat 8) (EVar 39); KWord (SA (EVar 39) (-24)) (N.to_nat 8) (ELit 112);
                              KWord (SA (EVar 32) 392) (N.to_nat 4) (EVar 40); KWord (SA (EVar 34) 0) (N.to_nat 4) (EVar 41);
                              KDisj (SA (EVar 34) 0) (ELit 4) (SA (EVar 32) 0) (ELit 880)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact Hvt | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact Hvb' | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [replace (w_sp w + 392) with (w_sp w + 272 + 112 + 8) by lia; exact Hfl | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [replace (w_words w + 0) with (w_words w) by lia; exact Cv0 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia |].
           destruct (Z.lt_ge_cases (w_words w + 0 + 4) (w_sp w + 0 + 1)) as [?|Hge]; [left; lia | right].
           destruct (W5 (w_words w) ltac:(unfold zwin; lia)) as [Hnw _]. unfold zwin in Hnw. lia. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia. clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite ext_val_sx4 in G11 by (destruct Cv0 as [Rv0 _]; cbn in Rv0; lia).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ (wbytes _ _ (word_to_le_bytes 4 ?fw)) _) _) _ => set (FW := fw) end.
    assert (EW : word_to_le_bytes 4 FW = word_to_le_bytes 4 (Z_to_bv 64 DS_FLHEX)) by (unfold FW; destruct Rfl as [-> | ->]; vm_compute; reflexivity).
    rewrite EW. clear EW FW.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mh := m) end.
    assert (STh : stores_in (zwin (w_sp w + 392) (w_sp w + 396)) M2 Mh) by (unfold Mh; stin).
    assert (Xh : PMX w A2 Mh model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ []))).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X2 | exact STh | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eassert (DSh : ds_rep A2 Mh (w_sp w + 272) (-4) _ B2).
    { unfold Mh. replace (w_sp w + 392) with (w_sp w + 272 + 112 + 8) by lia. exact HEX. }
    clear STh X2 DS2 HEX Hvt Hvb Hvb' Hfl. clearbody Mh. rename Xh into X2. rename DSh into DS2. destruct Cv0 as [Rv0 _]. cbn in Rv0.
    eapply (pm_put_u32 w c0 K fx A2 Mh model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R9 (-4) _ (v0) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-4) _ 0x11095 2 2 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    eapply (pm_tail_68410 w c0 K fx A4 M4 model4 _ R4c (-4) _ B4);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | exact DS4 | lia | exact FZ
      | exact Qsp | exact Qgp | exact Qtp].
  Qed.

  Lemma pm_D4 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x68434 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (zwin (w_sp w) (w_sp w + 776)) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-1) (w_sp w + 224) (w_sp w + 160) (w_sp w + 752) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C752 : cellw SEGS M1 (w_sp w + 752) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 752) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C160 : cellw SEGS M1 (w_sp w + 160) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 160) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 752) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 160) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C752 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C160 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear C752 C160.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-1) _ 0x126ba 46 46 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    eapply (pm_tail_68410 w c0 K fx A2 M2 model2 _ R2c (-1) _ B2);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | exact DS2 | lia | exact FZ
      | exact Qsp | exact Qgp | exact Qtp].
  Qed.
End PM.
End PmHdrDiagS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmHdrS1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrDiagS1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepS1.pmx_ds_room CL).
  #[local] Notation pm_tail_68410 := (PmStepS1.pm_tail_68410 CL).
  #[local] Notation cregs_kept := (PmStepS1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepS1.pm_put_cstr CL).
  #[local] Notation pm_put_num := (PmStepS1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepS1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepS1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepS1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepS1.pm_put_int CL).
  #[local] Notation pm_ctor := (PmStepS1.pm_ctor CL).
  #[local] Notation pm_pdiag := (PmStepS1.pm_pdiag CL).
  #[local] Notation pm_pdiag0 := (PmStepS1.pm_pdiag0 CL).
  #[local] Notation pm_pdiagE := (PmStepS1.pm_pdiagE CL).
  #[local] Notation pm_dtor := (PmStepS1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepS1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepS1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepS1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepS1.pm_binend CL).
  #[local] Notation pm_D1 := (PmHdrDiagS1.pm_D1 CL).
  #[local] Notation pm_D2 := (PmHdrDiagS1.pm_D2 CL).
  #[local] Notation pm_D3 := (PmHdrDiagS1.pm_D3 CL).
  #[local] Notation pm_D4 := (PmHdrDiagS1.pm_D4 CL).

  Lemma pm_hdrB : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> 5 <= w_n w -> c_widx c <= 5 -> c_endian c < 2 -> c_icount c = 0 ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    (forall A' M' model' c' R', PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> c_widx c' = 5 -> 5 <= w_n w -> c_endian c' < 2 -> c_icount c' = 0 ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c ->
        loop_regs w R' -> loop_mem w M' -> srealizes SEGS (cfg fx R' 0x66c78 M' model') K) ->
    srealizes SEGS (cfg fx R 0x66b38 M model) K.
  Proof using AC MI ST.
    intros w c0 K fx A M model c R PS X Htr BUD Hn5 Hw5 He2 Hic Qs0 Qsp Qgp Qtp LOOPK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (fld_cellw M _ 8 _ (x_hdrfn X) ltac:(lia)) as Ch.
    pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 33) 24) (N.to_nat 8) (ELit 0)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Ch | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (24%bv) G24.
    rewrite w_add in G9, G18, G19, G20, G21, G22 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite !w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
    assert (ST1 : stores_in (fun a => zwin (w_sp w + 16) (w_sp w + 144) a \/ zwin (w_p w + 72) (w_p w + 80) a) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model (set_scal c 5 (c_icount c) (c_endian c) (c_reqconv c))).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
        [exact X | exact ST1 | intros a [Ha|Ha]; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; [left; lia | right; lia]
        | unfold M1, O_WIDX; rdback
        | eapply fld_keep; [exact ST1 | exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST1 | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST1 | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
        | lia | lia | lia | exact Sc4]. }
    eapply (LOOPK A M1 model _ R1 X1); [cbn [c_tr set_scal]; exact Htr | exact BUD | reflexivity | exact Hn5 | cbn [c_endian set_scal]; exact He2 | cbn [c_icount set_scal]; exact Hic | reflexivity | reflexivity | reflexivity | |].
    - unfold loop_regs. rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G24. repeat split; reflexivity.
    - unfold loop_mem, hdr_consts. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold M1; rdback.
  Qed.

#[local] Definition HTPmLoopS1_0 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (19%bv, EVar 39); (10%bv, EVar 40)].
  Lemma pm_hdr : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_words w <> 0 -> c_widx c <= 5 -> c_icount c = 0 ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    (forall A' M' model' c' R', PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> c_widx c' = 5 -> 5 <= w_n w -> c_endian c' < 2 -> c_icount c' = 0 ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c ->
        loop_regs w R' -> loop_mem w M' -> srealizes SEGS (cfg fx R' 0x66c78 M' model') K) ->
    srealizes SEGS (cfg fx R 0x66854 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD Hw Hw5 Hic FZ Qs0 Qa0 Qsp Qgp Qtp LOOPK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5). pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    destruct (Z.lt_ge_cases (w_n w) 5) as [Hn4|Hn5].
    {
      pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 33)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x66868 :: STOPS) (SCR [false; false] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. clear HRn HR HK. fixregs.
      rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_D2 w c0 K fx A M model c R1); [exact PS | exact X | exact Htr | exact BUD | lia | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }
    pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [false; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10, G11 by lia. clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
    assert (ST1 : stores_in (zwin (w_sp w + 144) (w_sp w + 160)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (pm_binend w A M1 model c fx R1 _ K X1 Hw ltac:(lia) ltac:(unfold M1; rdback) ltac:(unfold M1; rdback) G10 G11 G2 G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear ST1. intros R2 M2 r e KEPT Hr Rr Re He2 X2 AG.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. clear G1 G2 G3 G4 G8 G10 G11 Qsp Qs0 Qa0 Qgp Qtp KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp.
    assert (F144 : fld SEGS M2 (w_sp w + 144) 8 (w_words w)).
    { eapply (fld_agree SEGS M1 M2); [lia | cbn; lia | unfold M1; rdback | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]]. }
    assert (F152 : fld SEGS M2 (w_sp w + 152) 8 (w_n w)).
    { eapply (fld_agree SEGS M1 M2); [lia | cbn; lia | unfold M1; rdback | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]]. }
    clear AG X1 X. clearbody M1. clear M1 MS. pose proof (x_ms X2) as MS.
    destruct (Z.eq_dec r 0) as [Hr0|Hr0].
    2: {
      pm_seed R2 w (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) [Z_to_bv 64 r].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M2 model (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) E X2.
      xruns HR HK 100%nat (0x669b0 :: STOPS) (SCR [false] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. clear HRn HR HK. fixregs.
      rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_D3 w c0 K fx A M2 model _ R3); [exact PS | exact X2 | cbn [c_tr set_scal]; exact Htr | exact BUD | exact Hw | lia | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }
    subst r. pose proof (He2 eq_refl) as He. clear He2. assert (He32 : 0 <= e < 2 ^ 32) by lia.

    pose proof (fld_cellw M2 _ 4 _ (x_endian X2) ltac:(cbn [c_endian set_scal]; lia)) as Ce. cbn [c_endian set_scal] in Ce. unfold O_ENDIAN in Ce.
    pm_seed R2 w (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) [Z_to_bv 64 0; Z_to_bv 64 e].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M2 model (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) E X2.
    apply (know_more E M2 [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite ext_val_sx4, sx32_small in G10 by lia.
    eapply (pm_is_host_endian w A M2 model _ fx R3 _ K X2 (ex_intro _ e (conj He32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4 KEPT (r01 & Hr01 & Ha0).
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. clear G1 G2 G3 G4 G8 G10 Qsp Qs0 Qgp Qtp KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp.

    destruct (mdef_cell4 M2 (w_words w) ltac:(eapply mdef_sub; [exact (x_wbuf X2 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (v0 & Cv0).
    destruct (mdef_cell4 M2 (w_words w + 4) ltac:(eapply mdef_sub; [exact (x_wbuf X2 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (v1 & Cv1).
    destruct (mdef_cell4 M2 (w_words w + 8) ltac:(eapply mdef_sub; [exact (x_wbuf X2 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (v2 & Cv2).
    destruct (mdef_cell4 M2 (w_words w + 12) ltac:(eapply mdef_sub; [exact (x_wbuf X2 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (v3 & Cv3).
    destruct (mdef_cell4 M2 (w_words w + 16) ltac:(eapply mdef_sub; [exact (x_wbuf X2 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (v4 & Cv4).
    pose proof (proj1 Cv0) as Rv0. pose proof (proj1 Cv1) as Rv1. pose proof (proj1 Cv2) as Rv2. pose proof (proj1 Cv3) as Rv3. pose proof (proj1 Cv4) as Rv4. cbn in Rv0, Rv1, Rv2, Rv3, Rv4.

    pm_seed R4 w (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) [Z_to_bv 64 r01; Z_to_bv 64 e; Z_to_bv 64 v0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R4. seedHK HK w A M2 model (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 32) 152) (N.to_nat 8) (EVar 35);
                           KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KWord (SA (EVar 34) 0) (N.to_nat 4) (EVar 41);
                           KRange (EVar 39) 0 1;
                           KDisj (SA (EVar 34) 0) (ELit 20) (SA (EVar 32) 0) (ELit 880); KDisj (SA (EVar 34) 0) (ELit 20) (SA (EVar 33) 0) (ELit 288)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact F152 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [replace (w_words w + 0) with (w_words w) by lia; exact Cv0 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia |].
           destruct (Z.lt_ge_cases (w_words w + 0 + 20) (w_sp w + 0 + 1)) as [?|Hge]; [left; lia | right].
           destruct (Z.lt_ge_cases (w_sp w + 0 + 880) (w_words w + 0 + 1)) as [?|Hge']; [lia | exfalso].
           destruct (Z.lt_ge_cases (w_words w) (w_sp w)) as [Hlt|Hle].
           + destruct (W5 (w_sp w) ltac:(unfold zwin; lia)) as [Hnw _]. unfold zwin in Hnw. lia.
           + destruct (W5 (w_words w) ltac:(unfold zwin; lia)) as [Hnw _]. unfold zwin in Hnw. lia.
         - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia |].
           destruct (Z.lt_ge_cases (w_words w + 0 + 20) (w_p w + 0 + 1)) as [?|Hge]; [left; lia | right].
           destruct (Z.lt_ge_cases (w_p w + 0 + 288) (w_words w + 0 + 1)) as [?|Hge']; [lia | exfalso].
           destruct (Z.lt_ge_cases (w_words w) (w_p w)) as [Hlt|Hle].
           + destruct (W5 (w_p w) ltac:(unfold zwin; lia)) as [_ Hnp]. lia.
           + destruct (W5 (w_words w) ltac:(unfold zwin; lia)) as [_ Hnp]. lia. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite ext_val_sx4 in G10 by lia. rewrite ext_val_sx4, sx32_small in G11, G19 by lia.
    rewrite (w_xor1 r01 Hr01).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) end.
    assert (ST3 : stores_in (zwin (w_p w + 92) (w_p w + 93)) M2 M3) by (unfold M3; stin).
    set (cc := set_scal c (c_widx c) (c_icount c) e (1 - r01)).
    assert (X3 : PMX w A M3 model cc).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img _ _ _ _ _ (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)));
        [exact X2 | exact ST3 | intros a Ha; right; unfold scal_win, zwin, O_WIDX, O_FLAGS in *; lia
        | eapply fld_keep; [exact ST3 | exact (x_widx X2) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST3 | exact (x_icount X2) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST3 | exact (x_endian X2) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | unfold M3, O_FLAGS; apply (flags_store M2 (w_p w) (c_reqconv c) (1 - r01) (x_flags X2)); [exact Sc4 | lia | lia | lia]
        | cbn [c_widx set_scal]; lia | cbn [c_widx c_icount set_scal]; lia | cbn [c_endian set_scal]; lia | lia]. }
    assert (F144' : fld SEGS M3 (w_sp w + 144) 8 (w_words w)).
    { eapply fld_keep; [exact ST3 | exact F144 | lia | cbn; lia | unfold zwin; cbn; intros; lia]. }
    assert (Cv1' : cell4 SEGS M3 (w_words w + 4) v1).
    { destruct Cv1 as [R1v F1v]. split; [exact R1v|]. eapply fld_keep; [exact ST3 | exact F1v | lia | cbn; lia | cbn; intros x Hx Hs].
      destruct (W5 x ltac:(unfold zwin; lia)) as [_ Hnp]. unfold zwin in Hs. lia. }
    assert (Cv2' : cell4 SEGS M3 (w_words w + 8) v2).
    { destruct Cv2 as [R1v F1v]. split; [exact R1v|]. eapply fld_keep; [exact ST3 | exact F1v | lia | cbn; lia | cbn; intros x Hx Hs].
      destruct (W5 x ltac:(unfold zwin; lia)) as [_ Hnp]. unfold zwin in Hs. lia. }
    assert (Cv3' : cell4 SEGS M3 (w_words w + 12) v3).
    { destruct Cv3 as [R1v F1v]. split; [exact R1v|]. eapply fld_keep; [exact ST3 | exact F1v | lia | cbn; lia | cbn; intros x Hx Hs].
      destruct (W5 x ltac:(unfold zwin; lia)) as [_ Hnp]. unfold zwin in Hs. lia. }
    assert (Cv4' : cell4 SEGS M3 (w_words w + 16) v4).
    { destruct Cv4 as [R1v F1v]. split; [exact R1v|]. eapply fld_keep; [exact ST3 | exact F1v | lia | cbn; lia | cbn; intros x Hx Hs].
      destruct (W5 x ltac:(unfold zwin; lia)) as [_ Hnp]. unfold zwin in Hs. lia. }
    clear ST3 X2 F144 F152 Ce Cv0 Cv1 Cv2 Cv3 Cv4. clearbody M3. rename F144' into F144. pose proof (x_ms X3) as MS3.

    eapply (pm_fixword w A M3 model cc fx R5 _ K X3 (ex_intro _ v0 (ex_intro _ e (conj Rv0 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R1r KEPT (r1 & Rr1 & Hr1). rewrite TablStmts.sx32_prs in Hr1.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G19 Qs3. clear G1 G2 G3 G4 G8 G10 G11 G19 Qsp Qs0 Qgp Qtp KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp.

    pm_seed R1r w cc [Z_to_bv 64 e; Z_to_bv 64 (PrsNeeds.sx32 r1); Z_to_bv 64 v1].
    seedHR HR E HTPmLoopS1_0 R1r. seedHK HK w A M3 model cc E X3.
    apply (know_more E M3 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) 4) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cv1' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6g. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. try rewrite ext_val_sx4 in G10 by lia.
    eapply (pm_fixword w A M3 model cc fx R6g _ K X3 (ex_intro _ v1 (ex_intro _ e (conj Rv1 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2r KEPT (r2 & Rr2 & Hr2). rewrite TablStmts.sx32_prs in Hr2.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G19 Qs3'. clear G1 G2 G3 G4 G8 G10 G11 G19 Qsp Qs0 Qgp Qtp Qs3 KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp. rename Qs3' into Qs3.

    destruct (Z.lt_ge_cases r2 (2 ^ 31)) as [Hr2lo|Hr2hi].
    2: {
      pose proof (land_sx32_hi r2 ltac:(lia)) as Hl0.
    pm_seed R2r w cc [Z_to_bv 64 e; Z_to_bv 64 (PrsNeeds.sx32 r2); Z_to_bv 64 v2].
    seedHR HR E HTPmLoopS1_0 R2r. seedHK HK w A M3 model cc E X3.
    apply (know_more E M3 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) 8) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cv2' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat (0x68434 :: STOPS) (SCR [false] [] []) 50%N. { split_scs; try sc_auto1. all: cbn [sc_denot]; evs. all: first [rewrite ver_br1 by (first [lia | apply sx32_range; lia]); first [apply Z.eqb_eq; assumption | apply Z.eqb_neq; assumption] | rewrite ver_br2 by lia; assumption]. }
    postrun. name_run HRn R7g. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. try rewrite ext_val_sx4 in G10 by lia.
      eapply (pm_D4 w c0 K fx A M3 model cc R7g); [exact PS | exact X3 | cbn [c_tr cc set_scal]; exact Htr | exact BUD | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }
    replace (PrsNeeds.sx32 r2) with r2 in Hr2 by (unfold PrsNeeds.sx32; destruct (Z.ltb_spec r2 (2 ^ 31)); lia).
    destruct (Z.eqb_spec (Z.land r2 18446744073692774655) 0) as [Hl0|Hl0].
    2: {
    pm_seed R2r w cc [Z_to_bv 64 e; Z_to_bv 64 r2; Z_to_bv 64 v2].
    seedHR HR E HTPmLoopS1_0 R2r. seedHK HK w A M3 model cc E X3.
    apply (know_more E M3 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) 8) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cv2' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat (0x68434 :: STOPS) (SCR [false] [] []) 50%N. { split_scs; try sc_auto1. all: cbn [sc_denot]; evs. all: first [rewrite ver_br1 by (first [lia | apply sx32_range; lia]); first [apply Z.eqb_eq; assumption | apply Z.eqb_neq; assumption] | rewrite ver_br2 by lia; assumption]. }
    postrun. name_run HRn R7g. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. try rewrite ext_val_sx4 in G10 by lia.
      eapply (pm_D4 w c0 K fx A M3 model cc R7g); [exact PS | exact X3 | cbn [c_tr cc set_scal]; exact Htr | exact BUD | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }
    destruct (Sumbool.sumbool_of_bool ((65536 <=? r2) && (r2 <=? 67072))) as [Hv|Hv].
    2: {
    pm_seed R2r w cc [Z_to_bv 64 e; Z_to_bv 64 r2; Z_to_bv 64 v2].
    seedHR HR E HTPmLoopS1_0 R2r. seedHK HK w A M3 model cc E X3.
    apply (know_more E M3 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) 8) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cv2' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat (0x68434 :: STOPS) (SCR [true; false] [] []) 50%N. { split_scs; try sc_auto1. all: cbn [sc_denot]; evs. all: first [rewrite ver_br1 by (first [lia | apply sx32_range; lia]); first [apply Z.eqb_eq; assumption | apply Z.eqb_neq; assumption] | rewrite ver_br2 by lia; assumption]. }
    postrun. name_run HRn R7g. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. try rewrite ext_val_sx4 in G10 by lia.
      eapply (pm_D4 w c0 K fx A M3 model cc R7g); [exact PS | exact X3 | cbn [c_tr cc set_scal]; exact Htr | exact BUD | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }

    pm_seed R2r w cc [Z_to_bv 64 e; Z_to_bv 64 r2; Z_to_bv 64 v2].
    seedHR HR E HTPmLoopS1_0 R2r. seedHK HK w A M3 model cc E X3.
    apply (know_more E M3 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) 8) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cv2' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. all: cbn [sc_denot]; evs. all: first [rewrite ver_br1 by (first [lia | apply sx32_range; lia]); first [apply Z.eqb_eq; assumption | apply Z.eqb_neq; assumption] | rewrite ver_br2 by lia; assumption]. }
    postrun. name_run HRn R7g. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. try rewrite ext_val_sx4 in G10 by lia.
    eapply (pm_fixword w A M3 model cc fx R7g _ K X3 (ex_intro _ v2 (ex_intro _ e (conj Rv2 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R3r KEPT (r3 & Rr3 & Hr3). rewrite TablStmts.sx32_prs in Hr3.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G19 Qs3'. clear G1 G2 G3 G4 G8 G10 G11 G19 Qsp Qs0 Qgp Qtp Qs3 KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp. rename Qs3' into Qs3.
    pm_seed R3r w cc [Z_to_bv 64 e; Z_to_bv 64 (PrsNeeds.sx32 r3); Z_to_bv 64 v3].
    seedHR HR E HTPmLoopS1_0 R3r. seedHK HK w A M3 model cc E X3.
    apply (know_more E M3 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) 12) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cv3' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8g. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. try rewrite ext_val_sx4 in G10 by lia.
    eapply (pm_fixword w A M3 model cc fx R8g _ K X3 (ex_intro _ v3 (ex_intro _ e (conj Rv3 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4r KEPT (r4 & Rr4 & Hr4). rewrite TablStmts.sx32_prs in Hr4.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G19 Qs3'. clear G1 G2 G3 G4 G8 G10 G11 G19 Qsp Qs0 Qgp Qtp Qs3 KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp. rename Qs3' into Qs3.
    pm_seed R4r w cc [Z_to_bv 64 e; Z_to_bv 64 (PrsNeeds.sx32 r4); Z_to_bv 64 v4].
    seedHR HR E HTPmLoopS1_0 R4r. seedHK HK w A M3 model cc E X3.
    apply (know_more E M3 [KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) 16) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact F144 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cv4' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9g. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (19%bv) G19.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. try rewrite ext_val_sx4 in G10 by lia.
    eapply (pm_fixword w A M3 model cc fx R9g _ K X3 (ex_intro _ v4 (ex_intro _ e (conj Rv4 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R5r KEPT (r5 & Rr5 & Hr5). rewrite TablStmts.sx32_prs in Hr5.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G19 Qs3'. clear G1 G2 G3 G4 G8 G10 G11 G19 Qsp Qs0 Qgp Qtp Qs3 KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp. rename Qs3' into Qs3.
    eapply (pm_hdrB w c0 K fx A M3 model cc R5r PS X3 ltac:(cbn [c_tr cc set_scal]; exact Htr) BUD Hn5 ltac:(cbn [c_widx cc set_scal]; exact Hw5) ltac:(cbn [c_endian cc set_scal]; lia) ltac:(cbn [c_icount cc set_scal]; exact Hic) Qs0 Qsp Qgp Qtp ltac:(intros A' M' model' c' R'; pose proof (LOOPK A' M' model' c' R') as LK; cbn [c_m1 c_m2 c_m3 cc set_scal] in LK; exact LK)).
  Qed.
End PM.
End PmHdrS1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrDiagS1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrS1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepS1.pmx_ds_room CL).
  #[local] Notation pm_tail_68410 := (PmStepS1.pm_tail_68410 CL).
  #[local] Notation cregs_kept := (PmStepS1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepS1.pm_put_cstr CL).
  #[local] Notation pm_put_num := (PmStepS1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepS1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepS1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepS1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepS1.pm_put_int CL).
  #[local] Notation pm_ctor := (PmStepS1.pm_ctor CL).
  #[local] Notation pm_pdiag := (PmStepS1.pm_pdiag CL).
  #[local] Notation pm_pdiag0 := (PmStepS1.pm_pdiag0 CL).
  #[local] Notation pm_pdiagE := (PmStepS1.pm_pdiagE CL).
  #[local] Notation pm_dtor := (PmStepS1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepS1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepS1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepS1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepS1.pm_binend CL).
  #[local] Notation pm_D1 := (PmHdrDiagS1.pm_D1 CL).
  #[local] Notation pm_D2 := (PmHdrDiagS1.pm_D2 CL).
  #[local] Notation pm_D3 := (PmHdrDiagS1.pm_D3 CL).
  #[local] Notation pm_D4 := (PmHdrDiagS1.pm_D4 CL).
  #[local] Notation pm_hdrB := (PmHdrS1.pm_hdrB CL).
  #[local] Notation pm_hdr := (PmHdrS1.pm_hdr CL).

  Definition nodes (c : pmc) : Z := Zlen (t3c (c_m1 c)) + Zlen (t3c (c_m2 c)) + Zlen (t3c (c_m3 c)).

  Definition m3ok (ents : list (Z * (Z * Z))) : Prop := Forall (fun e => 0 <= snd (snd e) < 2 ^ 31) ents.
  Lemma m3ok_val : forall ents p k v, m3ok ents -> In (p, (k, v)) ents -> 0 <= v < 2 ^ 31.
  Proof using. intros ents p k v H Hin. exact (proj1 (Forall_forall _ _) H (p, (k, v)) Hin). Qed.

  Definition macct (c : pmc) : Prop :=
    8 * t3b (c_m1 c) <= 16 * Zlen (t3c (c_m1 c)) + 504 /\ 8 * t3b (c_m2 c) <= 16 * Zlen (t3c (c_m2 c)) + 504 /\
    8 * t3b (c_m3 c) <= 16 * Zlen (t3c (c_m3 c)) + 504 /\ m3ok (t3c (c_m3 c)).

  Definition lacc (c : pmc) : Prop :=
    2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c.
  Definition LI (w : pmw MI ST) A M model c R : Prop :=
    PMX w A M model c /\ c_tr c = [] /\ pm_bud (w_n w) c /\ loop_regs w R /\ loop_mem w M /\ c_icount c + 5 <= c_widx c /\ c_endian c < 2 /\ w_words w <> 0
    /\ nodes c + 1 <= c_widx c + 3 /\ macct c /\ lacc c.

  Lemma pm_ret : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (r : word),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> frm_zero (@fp_csr fx) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 26%bv = r ->
    srealizes SEGS (cfg fx R 0x684c0 M model) K.
  Proof using AC MI ST.
    intros w c0 K fx A M model c R r PS X Htr BUD FZ Qsp Qgp Qtp Hs10.
    destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    eapply (pm_exit w c0 K fx A M model c R r X Htr).
    - unfold OPND_SZ in B5. lia. - lia. - lia.
    - exact (ps_diag _ _ _ PS).
    - intros b Hb. eapply (pm_bud_sizes SEGS Ly.L MI ST w A M model c); [exact X | | exact Hb]. repeat (split; [assumption|]). exact B9.
    - intros cls. pose proof (x_geo X) as GEO'. destruct GEO' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn' & _).
      pose proof (ps_cls _ _ _ PS) as HCL0.
      eapply (cnt_c_blocks SEGS Ly.L MI (proj1 HCL0) (proj1 (proj2 HCL0)) (proj2 (proj2 HCL0))); [repeat (split; [assumption|]); exact B9 | lia].
    - exact (ps_L0 _ _ _ PS).
    - exact FZ.
    - exact (ps_post _ _ _ PS).
    - exact Qsp.
    - rewrite (ps_gp _ _ _ PS). exact Qgp.
    - rewrite (ps_tp _ _ _ PS). exact Qtp.
    - exact Hs10.
    - exact (ps_ret _ _ _ PS). - exact (ps_R0ra _ _ _ PS). - exact (ps_R0sp _ _ _ PS).
  Qed.

  Lemma sextw_sxw : forall e, 0 <= e < 2 ^ 32 -> sext 64 (alu32 ALU_ADD (low32 (sxw e)) (low32 (Z_to_bv 64 0))) = sxw e.
  Proof using.
    intros e He. rewrite w_addw. unfold v_addw, sxw. rewrite (u64_of_Z 0) by lia. rewrite Z.add_0_r.
    rewrite (bv_swrap32_cases e) by lia. destruct (Z.ltb_spec e (2 ^ 31)).
    - rewrite u64_of_Z by lia. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec e (2 ^ 31)); [reflexivity | lia].
    - rewrite <- (Z_to_bv64_add_mod (e - 2 ^ 32)) at 1. rewrite u64_of_Z by lia.
      replace (e - 2 ^ 32 + 2 ^ 64) with (e + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite swrap32_shift.
      rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec e (2 ^ 31)); [lia|]. reflexivity.
  Qed.

  Lemma pm_latch_err : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (e : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> frm_zero (@fp_csr fx) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 26%bv = sxw e -> 0 < e < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x66c6c M model) K.
  Proof using AC MI ST.
    intros w c0 K fx A M model c R e PS X Htr BUD FZ Qsp Qgp Qtp Hs10 He.
    pose proof (x_ms X) as MS.
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); sxw e]).
    seedHR HR E [(2%bv, EVar 32); (26%bv, EVar 33)] R.
    assert (HK : know_ok SEGS E M []) by (apply Forall_nil).
    xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs. rewrite sextw_sxw by lia. change (Z_to_bv 64 0) with (sxw 0). rewrite br_eq_sxw by lia. bool_lia. }
    postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (26%bv) G26. clear HRn HR HK. fixregs.
    rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_ret w c0 K fx A M model c R1); [exact PS | exact X | exact Htr | exact BUD | exact FZ | exact G2 | exact G3 | exact G4 | exact G26].
  Qed.

  Ltac lregs := unfold loop_regs; repeat split; first [assumption | etransitivity; [eassumption|]; first [assumption | reflexivity]].

  Lemma pm_latch_ok : forall (w : pmw MI ST) (fx : FPState) A M model c R K,
    PMX w A M model c -> loop_regs w R -> getr R 26%bv = Z_to_bv 64 0 ->
    (forall R', loop_regs w R' -> getr R' 26%bv = Z_to_bv 64 0 -> srealizes SEGS (cfg fx R' 0x66c78 M model) K) ->
    srealizes SEGS (cfg fx R 0x66c6c M model) K.
  Proof using AC MI ST.
    intros w fx A M model c R K X LR Hs10 HEADK. pose proof (x_ms X) as MS.
    destruct LR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs6 & Qs8).
    pose (E := Eseed R [Z_to_bv 64 (w_sp w)]).
    seedHR HR E [(2%bv, EVar 32); (26%bv, ELit 0)] R.
    assert (HK : know_ok SEGS E M []) by (apply Forall_nil).
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (24%bv) G24. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs.
    apply HEADK; [lregs | exact G26].
  Qed.

  Definition body_stmt (w : pmw MI ST) (c0 : parserC) (K : TSet) (fx : FPState) : Prop :=
    forall A M model c R,
      LI w A M model c R -> c_widx c < w_n w -> getr R 10%bv = Z_to_bv 64 (c_widx c) ->
      (forall (fx' : FPState) A' M' model' c' R', frm_zero (@fp_csr fx') -> LI w A' M' model' c' R' -> c_widx c < c_widx c' ->
          srealizes SEGS (cfg fx' R' 0x66c78 M' model') K) ->
      srealizes SEGS (cfg fx R 0x66c88 M model) K.

  Lemma pm_loop : forall (w : pmw MI ST) c0 K,
    PMS w c0 K -> (forall fx : FPState, frm_zero (@fp_csr fx) -> body_stmt w c0 K fx) ->
    forall (fx : FPState) A M model c R, frm_zero (@fp_csr fx) -> LI w A M model c R -> srealizes SEGS (cfg fx R 0x66c78 M model) K.
  Proof using AC MI ST.
    intros w c0 K PS BODYf fx A M model c R FZ HLI.
    remember (Z.to_nat (w_n w - c_widx c)) as n eqn:Hn. revert fx FZ A M model c R HLI Hn.
    induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros fx FZ A M model c R HLI Hn. pose proof (BODYf fx FZ) as BODY.
    destruct HLI as (X & Htr & BUD & LR & LM & Hw5 & He2 & HwN & ACC & MACC).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs6 & Qs8).
    destruct (Z.lt_ge_cases (c_widx c) (w_n w)) as [Hlt|Hge].
    -
      pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x66c88 :: STOPS) (SCR [true] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (24%bv) G24. rreg HRn (10%bv) G10.
      clear HRn HR HK. fixregs.
      eapply (BODY A M model c R1).
      + split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [| split; [exact LM | split; [exact Hw5 | split; [exact He2 | split; [exact HwN | split; [exact ACC | exact MACC]]]]]].
        lregs.
      + exact Hlt.
      + exact G10.
      + intros fx' A' M' model' c' R' FZ' HLI' Hprog. destruct HLI' as (X' & HLI'). pose proof (x_scal X') as (Sc1' & _).
        eapply (IH (Z.to_nat (w_n w - c_widx c'))); [lia | exact FZ' | split; [exact X' | exact HLI'] | reflexivity].
    -
      pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (26%bv) G26. clear HRn HR HK. fixregs.
      rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_ret w c0 K fx A M model c R1); [exact PS | exact X | exact Htr | exact BUD | exact FZ | exact G2 | exact G3 | exact G4 | exact G26].
  Qed.

  Lemma init_bud : forall (c0 : parserC) n,
    fresh_state (pc_state c0) (st_words (pc_state c0)) (st_nwords (pc_state c0)) -> 0 <= n ->
    pm_bud n (PmCoreS1.init_pmc c0).
  Proof using.
    intros c0 n FR Hn. destruct FR as (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
    unfold pm_bud, PmCoreS1.init_pmc. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd pc_state].
    rewrite Hm1, Hm2, Hm3. unfold t3b, t3c, Zlength, OPND_SZ. cbn [fst snd length Z.of_nat].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); try lia. intros b [].
  Qed.

  #[local] Notation HCL := (cl_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma pm_main :
    (forall (w : pmw MI ST) c0 K (fx : FPState), PMS w c0 K -> frm_zero (@fp_csr fx) -> body_stmt w c0 K fx) ->
    parse_module_stmt SEGS Ly.L MI ST kcS1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros BODY. unfold parse_module_stmt. cbn [kc_pm_stack kc_parse_module kcS1].
    intros fx A s R M model sp ret p c0 L0 K CB ROC FZ Ha0 PR ASP ASC CAL FR WOK WDJ PERM BUD POST.
    eapply (PmCoreS1.pm_prologue MI ST fx A s R M model sp ret p c0 L0 K CB ROC Ha0 PR ASP ASC FR WOK WDJ PERM BUD).
    intros M1 R1 X Q8 Q10 Q2 Q3 Q4.
    destruct CB as [AI MS ROCI SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx]. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    pose proof BUD as BUD'. destruct BUD' as (Bcaps & Bbig & Bnmax & Bn & BS & BN & BB).
    assert (CNT : forall cls, count_class_f (size_class MI) (BIG MI) L0 cls <= count_class_f (size_class MI) (BIG MI) L0 cls) by (intros; lia).
    assert (BBF : big_bytes_f (round_big MI) (BIG MI) L0 <= big_bytes_f (round_big MI) (BIG MI) L0) by lia.
    assert (PS : PMS (PmCoreS1.mkw MI ST sp 16384 ret p c0 L0 R A M model s) c0 K).
    { constructor; cbn [PmCoreS1.mkw w_A0 w_L0 w_n w_diag w_ret w_R0 w_sp0 w_sp w_STK].
      - exact PERM.
      - intros cls Hc. pose proof (BS cls Hc). pose proof (CNT cls). lia.
      - intros cls Hc. pose proof (BN cls Hc). pose proof (CNT cls). lia.
      - lia.
      - destruct PR as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd]. pose proof (proj1 (sr_w2 _ _ _ _ _ _ _ Pst)) as Hd. cbn in Hd. lia.
      - unfold PmCoreS1.POSTK, w_sp0. cbn [PmCoreS1.mkw w_s w_R0 w_model0 w_p w_cons w_words w_n w_L0 w_A0 w_M0 w_ret w_STK w_sp]. unfold PM_FRAME.
        replace (sp - 880 + 880 - 16384) with (sp - 16384) by lia. replace (sp - 880 + 880) with sp by lia. exact POST.
      - exact Hret. - exact Hra. - unfold w_sp0. cbn [w_sp PmCoreS1.mkw]. unfold PM_FRAME. rewrite Hsp. f_equal. lia. - exact Hgp. - exact Htp.
      - exact (cl_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL). }
    set (w := PmCoreS1.mkw MI ST sp 16384 ret p c0 L0 R A M model s) in *.
    assert (Hn0 : 0 <= w_n w) by (subst w; cbn [w_n PmCoreS1.mkw]; lia).
    pose proof (init_bud c0 (w_n w) FR Hn0) as BUD0.
    pose proof FR as FR'. destruct FR' as (Fw & Fn & Fwi & Fic & Ffl & _).
    destruct (Z.eq_dec (st_words (pc_state c0)) 0) as [Hw0|Hw0].
    - eapply (pm_D1 w c0 K fx A M1 model (PmCoreS1.init_pmc c0) R1 PS X eq_refl BUD0 Hw0 FZ Q8 Q10);
        [exact Q2 | rewrite Q3; exact Hgp | rewrite Q4; exact Htp].
    - eapply (pm_hdr w c0 K fx A M1 model (PmCoreS1.init_pmc c0) R1 PS X eq_refl BUD0 Hw0);
        [cbn; lia | cbn; lia | exact FZ | exact Q8 | exact Q10 | exact Q2 | rewrite Q3; exact Hgp | rewrite Q4; exact Htp |].
      intros A' M' model' c' R' X' Htr' BUD' Hw5 Hn5 He2 Hic Em1 Em2 Em3 LR LM.
      eapply (pm_loop w c0 K PS (fun fx1 FZ1 => BODY w c0 K fx1 PS FZ1) fx); [exact FZ|].
      split; [exact X'|]. split; [exact Htr'|]. split; [exact BUD'|]. split; [exact LR|]. split; [exact LM|]. split; [lia|]. split; [exact He2|]. split; [unfold w; cbn [w_words PmCoreS1.mkw]; exact Hw0|].
      destruct FR as (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & _).
      unfold nodes, macct, m3ok, lacc. rewrite Em1, Em2, Em3. unfold PmCoreS1.init_pmc. cbn [c_m1 c_m2 c_m3]. rewrite Hm1, Hm2, Hm3. unfold Zlen. cbn [t3b t3c fst snd length Z.of_nat]. repeat split; try lia. apply Forall_nil.
  Qed.
End PM.
