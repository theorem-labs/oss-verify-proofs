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
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep5S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitDiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOHeadS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmDispatchS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_MaskS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmArm_IdS1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4S1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation nodes := (PmLoopS1.nodes).
  #[local] Notation macct := (PmLoopS1.macct).
  #[local] Notation GOK := (cl_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cl_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cl_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsS1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsS1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsS1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsS1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).
  Definition pm_is_ext_inst := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_is_ext_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma w2le4_sxw : forall v, word_to_le_bytes 4 (sxw v) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v. unfold sxw. change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N. apply word_to_le_bytes_swrap. cbn; lia. Qed.

  Lemma id_diag0 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x676e8 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagE w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | split; [exact G13 | lia] |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x140dd 7 7 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M2 (w_sp w + 272 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R2cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R2cd (-10) _ _ B2 []);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  Lemma id_diag1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> cellw SEGS M (w_sp w + 680) 4 wv ->
    srealizes SEGS (cfg fx R 0x6789c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R wv PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C680.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C680) as Hwv. cbn in Hwv.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagE w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | split; [exact G13 | lia] |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C680; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x1423a 17 17 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in C680; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C680. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-10) _ (wv) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in C680; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-10) _ 0x13428 48 48 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS4) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M4 (w_sp w + 272 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R4cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R4cd (-10) _ _ B4 []);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | rewrite Zlength_nil; lia | exact DS4 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  Theorem arm_ID_S1 : forall t, (t = 1 \/ t = 42) -> arm_stmt t 0x67308.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht12 w c0 K fx I A M model c R wv PS FZ IP HAE PK CK AACC. specialize (PK fx FZ). specialize (CK fx FZ).
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q18 & Q21 & Q22 & Q23 & Q25 & PO & C680).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof (ipure_ranges I IP) as (Riwc & Rop).
    destruct PO as (_ & C686 & _).
    assert (Q18' : getr R 18%bv = sxw wv) by (rewrite Q18; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q18z : getr R 18%bv = Z_to_bv 64 0) by (rewrite Q18', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, ELit 0)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x676e8 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      exact (id_diag0 w c0 K fx A M model c R1 PS FZ CK X Htr BUD G2 G3 G4 G8).
    -
      pm_seed R w c [Z_to_bv 64 (c_widx c - i_io I); sxw wv; Z_to_bv 64 (i_op I)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (18%bv, EVar 40); (25%bv, EVar 41)] R. seedHK HK w A M model c E X.
      apply (know_more E M [KRange (EVar 39) 0 65535]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_eq_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (18%bv) G18.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [21; 23]%bv HRn eq_refl) as GK1. rreg HRn (25%bv) G25.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      rewrite Qgp in G3. rewrite Qtp in G4.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 688) (w_sp w + 692)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 688) (w_sp w + 692)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 688) (w_sp w + 692) a) M M1).
      { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
      assert (LM1 : loop_mem w M1) by (eapply (PmBody1S1.loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (C686' : cellw SEGS M1 (w_sp w + 686) 2 1).
      { eapply (PmBody1S1.cellw_frame M M1); [exact C686 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      assert (C680' : cellw SEGS M1 (w_sp w + 680) 4 wv).
      { eapply (PmBody1S1.cellw_frame M M1); [exact C680 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.

      assert (PUSH1 : forall Rx, oregs w Rx -> getr Rx 21%bv = Z_to_bv 64 t -> getr Rx 23%bv = Z_to_bv 64 (i_io I) -> getr Rx 25%bv = Z_to_bv 64 (i_op I) ->
                      srealizes SEGS (cfg fx Rx 0x670c4 M1 model) K).
      { intros Rx ORx X21 X23 X25. eapply (PK A M1 model c Rx 1 []).
        - split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact ORx|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
          split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
        - exact X21. - exact X23. - exact X25. - exact C686'. - left; lia.
        - reflexivity. - reflexivity. - reflexivity.
        - change (Z.min 1 1) with 1. lia.
        - rewrite app_nil_r. reflexivity. - exact PmZw.seed_free_nil. - rewrite PmZw.Zlen_nil. lia. - left; reflexivity.
        - reflexivity. - left; reflexivity. - left; reflexivity. - intros []. }
      assert (Rop32 : 0 <= i_op I < 2 ^ 32) by lia.
      eapply (pm_is_ext_inst w A M1 model c fx R1 _ K X1 (ex_intro _ (i_op I) (conj Rop32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 KEPT (b & Hb).
      keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G18 Q18b. keptQ KEPT G25 Q25b.
      pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
      assert (GK2 : forall r', In r' [21; 23]%bv -> getr R2 r' = getr R r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
      clear KEPT G1 G2 G3 G4 G8 G10 G18 G25 GK1 OR1.

      pm_seed R2 w c [Z_to_bv 64 (c_widx c - i_io I); Z_to_bv 64 (if b then 1 else 0)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39); (10%bv, EVar 40)] R2. seedHK HK w A M1 model c E X1.
      destruct (Z.eq_dec (c_widx c - i_io I) 3) as [Ho3 | Hon3].
      2: { xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N. { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite br_ne by lia; bool_lia. }
           postrun. name_run HRn R3.
           rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
           pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
           pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK3.
           clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
           apply (PUSH1 R3 OR3).
           - rewrite (GK3 21%bv), (GK2 21%bv) by (clear; inl). exact Q21.
           - rewrite (GK3 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
           - rewrite (GK3 25%bv) by (clear; inl). exact Q25b. }
      apply (know_more E M1 [KRange (EVar 40) (if b then 1 else 0) (if b then 1 else 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | destruct b; lia | destruct b; lia]. }
      destruct b.
      2: {
           xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite br_ne by lia; bool_lia. }
           postrun. name_run HRn R3.
           rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
           pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
           pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK3.
           clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
           apply (PUSH1 R3 OR3).
           - rewrite (GK3 21%bv), (GK2 21%bv) by (clear; inl). exact Q21.
           - rewrite (GK3 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
           - rewrite (GK3 25%bv) by (clear; inl). exact Q25b. }

      pose proof (PmBody1S1.loop_mem_cell w M1 32 (w_p w + 176) LM1 ltac:((first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ])) ltac:(lia)) as C32.
      apply (know_more E M1 [KWord (SA (EVar 32) 32) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 176))]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [exact C32 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite br_ne by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK3.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite w_add in G10, G11 by lia.
      eapply (pm_find_m3 w A M1 model c fx R3 (w_sp w + 680) wv 0x67338 K X1 ltac:(unfold O_M3; exact G10) G11 C680' ltac:(lia) ltac:(lia) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 p KEPT Hp Hfound.
      keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4.
      pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
      assert (GK4 : forall r', In r' [21; 23; 25]%bv -> getr R4 r' = getr R2 r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK3. exact Hr'. }
      clear KEPT G1 G2 G3 G4 G8 G10 G11 GK3 OR3.
      destruct Hfound as [-> | (Hp0 & Hp47 & Hpal & v & Hin & Cv)].
      +
        pm_seed R4 w c (@nil word).
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R4. seedHK HK w A M1 model c E X1.
        xruns HR HK 100%nat (0x6789c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
        clear HRn HR HK. fixregs. rewrite Qgp4 in G3. rewrite Qtp4 in G4.
        exact (id_diag1 w c0 K fx A M1 model c R5 wv PS FZ CK X1 Htr BUD G2 G3 G4 G8 C680').
      +
        pose proof (proj1 Cv) as Hv. cbn in Hv.
        pm_seed R4 w c [Z_to_bv 64 p; sxw v].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R4. seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KRange (EVar 39) 1 (2 ^ 47)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cv. }
        postrun. name_run HRn R5.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
        rewrite w2le4_sxw.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
        assert (ST2 : stores_in (zwin (w_sp w + 236) (w_sp w + 240)) M1 M2) by (unfold M2; stin).
        assert (X2 : PMX w A M2 model c).
        { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 M2 model c (zwin (w_sp w + 236) (w_sp w + 240)));
            [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
        assert (AG2 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 236) (w_sp w + 240) a) M1 M2).
        { eapply stores_in_agree; [exact ST2 | intros b' Hb'; unfold zwin in *; lia]. }
        assert (FR2 : ifr w M2) by (unfold M2; apply ifr_store4; [exact FR1 | left; split; [reflexivity | exact (proj2 (PmLoopS1.m3ok_val _ _ _ _ (proj2 (proj2 (proj2 MAC))) Hin))] | lia | lia | lia]).
        eapply (PK A M2 model c R5 1 []).
        * split; [exact X2|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR5|].
          split; [eapply (PmBody1S1.loop_mem_frame w M1 M2); [exact LM1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]|].
          split; [eapply (PmBody1S1.ictx_agree w M1 M2); [exact IC1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]|].
          split; [exact FR2|]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
        * rewrite (GK5 21%bv), (GK4 21%bv), (GK2 21%bv) by (clear; inl). exact Q21.
        * rewrite (GK5 23%bv), (GK4 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
        * rewrite (GK5 25%bv), (GK4 25%bv) by (clear; inl). exact Q25b.
        * eapply (PmBody1S1.cellw_frame M1 M2); [exact C686' | lia | cbn; lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]].
        * left; lia.
        * reflexivity. * reflexivity. * reflexivity.
        * change (Z.min 1 1) with 1. lia.
        * rewrite app_nil_r. reflexivity. * exact PmZw.seed_free_nil. * rewrite PmZw.Zlen_nil. lia. * left; reflexivity.
        * reflexivity. * left; reflexivity. * left; reflexivity. * intros [].
  Qed.
End PM.
End PmArm_IdS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_SpecS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmArm_ExtS1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_SpecS1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation nodes := (PmLoopS1.nodes).
  #[local] Notation macct := (PmLoopS1.macct).
  #[local] Notation GOK := (cl_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cl_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cl_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsS1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsS1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsS1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsS1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_oty_pb := (PmStep4S1.pm_oty_pb CL).
  #[local] Notation pm_span_push := (PmArm_SpecS1.pm_span_push CL).
  Definition pm_is_nonsemantic := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_is_nonsemantic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma seed_free_52 : seed_free [OT_VARIABLE_ID].
  Proof using. intros t [<- | []]. reflexivity. Qed.

  Lemma ext_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 18%bv = sxw wv -> 0 <= wv < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x67964 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R wv PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 Q18 Hwv.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_pdiag0 w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | reflexivity |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10e05 37 37 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (wv) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS3) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M3 (w_sp w + 272 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R3cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R3cd (-4) _ _ B3 []);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | rewrite Zlength_nil; lia | exact DS3 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  Theorem arm_EXTNUM_S1 : arm_stmt 7 0x67528.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R wv PS FZ IP HAE PK CK AACC. specialize (PK fx FZ). specialize (CK fx FZ).
    pose proof (AE_facts w I A M model c R 7 wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q18 & Q21 & Q22 & Q23 & Q25 & PO & C680).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof MAXLEN as Hml. unfold V3MAX in V3B.
    destruct PO as (_ & C686 & _).
    destruct (ifr_ext w M FR) as (ext & Cext & Hext).
    assert (Q18' : getr R 18%bv = sxw wv) by (rewrite Q18; symmetry; apply sxw_sx32; lia).
    assert (Ht36 : 7 <> OT_RESULT_ID /\ 7 <> OT_LITERAL_INTEGER /\ 7 <> OT_LITERAL_STRING) by (unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING; lia).

    pm_seed R w c [sxw ext; sxw wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 40)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cext. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK1. rreg HRn (18%bv) G18.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G12 by lia. rewrite (sxw_small' ext) in G10 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 752) (w_sp w + 760)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 752) (w_sp w + 760)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    pose proof (x_ms X1) as MS1.
    eapply (pm_lookup_ext w A M1 model c fx R1 ext wv (w_sp w + 752) _ K X1 G10 ltac:(lia) ltac:(intros HH; discriminate HH)
              ltac:(intros _; split; [rewrite G11, TablStmts.sx32_prs; apply sxw_sx32; lia | split; [lia | exact G12]]) G2 ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)
              ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 M2 r d KEPT Hr Rr Fd Hfound Hhnd X2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G18 Q18b.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    assert (GK2 : forall r', In r' [21; 23; 25]%bv -> getr R2 r' = getr R r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
    clear KEPT G1 G2 G3 G4 G8 G10 G11 G12 G18 GK1 OR1.
    assert (AG02 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 752) (w_sp w + 760) a) M M2).
    { intros a Ha. rewrite (AG a ltac:(unfold w_sp0, PM_FRAME, zwin in *; lia)). apply (stores_in_agree _ _ _ _ ST1 ltac:(intros b Hb; exact Hb)). unfold zwin in *. lia. }
    assert (LM2 : loop_mem w M2) by (eapply (PmBody1S1.loop_mem_frame w M M2); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (IC2 : ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M M2); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (FR2 : ifr w M2) by (eapply (ifr_agree w M M2); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (C686_2 : cellw SEGS M2 (w_sp w + 686) 2 1).
    { eapply (PmBody1S1.cellw_frame M M2); [exact C686 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    assert (Cext2 : cellw SEGS M2 (w_sp w + 236) 4 ext).
    { eapply (PmBody1S1.cellw_frame M M2); [exact Cext | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    pose proof (x_ms X2) as MS2. clear ST1 X1 MS1 AG AG02 MS X LM IC FR C686 C680 Cext.
    assert (OB2 : forall Rx, oregs w Rx -> OBASE w I A M2 model c Rx).
    { intros Rx ORx. split; [exact X2|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact ORx|]. split; [exact LM2|]. split; [exact IC2|]. split; [exact FR2|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R]. }

    pm_seed R2 w c [Z_to_bv 64 r; sxw ext].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M2 model c E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cext2. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [18; 21; 23; 25]%bv HRn eq_refl) as GK3.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
    rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite (sxw_small' ext) in G10 by lia.
    assert (Hext32 : 0 <= ext < 2 ^ 32) by lia.
    eapply (pm_is_nonsemantic w A M2 model c fx R3 _ K X2 (ex_intro _ ext (conj Hext32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4 KEPT (b & Hb).
    keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4. keptQ KEPT G22 Q22r.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
    assert (GK4 : forall r', In r' [18; 21; 23; 25]%bv -> getr R4 r' = getr R2 r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK3. exact Hr'. }
    clear KEPT G1 G2 G3 G4 G8 G10 G22 GK3 OR3.
    assert (Qs44 : getr R4 20%bv = Z_to_bv 64 (w_p w + 264)) by (destruct OR4 as (_ & _ & _ & _ & _ & _ & Q & _); exact Q).

    assert (PB52 : forall Rx M3 (ret : Z),
              oregs w Rx -> (forall r', In r' [18; 21; 23; 25]%bv -> getr Rx r' = getr R2 r') ->
              getr Rx 1%bv = Z_to_bv 64 ret -> (ret = 0x67570 \/ ret = 0x67804) ->
              getr Rx 10%bv = Z_to_bv 64 (w_p w + 264) -> getr Rx 11%bv = Z_to_bv 64 (w_sp w + 272) ->
              stores_in (zwin (w_sp w + 272) (w_sp w + 276)) M2 M3 -> fld SEGS M3 (w_sp w + 272) 4 52 ->
              (forall A' R' M' model' (b' cap' : Z),
                  OBASE w I A' M' model' (set_v3 c (b', t3b (c_v3 c) ++ [OT_VARIABLE_ID], cap')) R' ->
                  (forall r', In r' [18; 21; 23; 25]%bv -> getr R' r' = getr R2 r') ->
                  cellw SEGS M' (w_sp w + 686) 2 1 -> fld SEGS M' (w_sp w + 752) 8 d ->
                  srealizes SEGS (cfg fx R' ret M' model') K) ->
              srealizes SEGS (cfg fx Rx 0x69844 M3 model) K).
    { intros Rx M3 ret ORx GKx Gra Hret Ga0 Ga1 ST3 F52 CONT.
      pose proof ORx as ORx'. destruct ORx' as (Xsp & Xgp & Xtp & Xs0 & _).
      assert (X3 : PMX w A M3 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M2 M3 model c (zwin (w_sp w + 272) (w_sp w + 276)));
          [exact X2 | exact ST3 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      eapply (pm_oty_pb w c0 K fx A M3 model c Rx (w_sp w + 272) 52 ret PS X3 Htr BUD).
      - split; [exact Gra|]. split; [destruct Hret as [-> | ->]; apply bv_eq; vm_compute; reflexivity|]. split; [lia|]. split; [exact Xsp|]. split; [exact Xgp | exact Xtp].
      - unfold O_V3. exact Ga0.
      - exact Ga1.
      - exact F52.
      - lia.
      - lia.
      - unfold w_sp0, PM_FRAME. lia.
      - intros Heq. unfold vgrow. rewrite <- Heq. lia.
      - intros A5 R5 M5 model5 b' cap' X5 BUD5 KEPT5 AG5.
        assert (AG25 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 272) (w_sp w + 276) a) M2 M5).
        { intros a Ha. rewrite (AG5 a ltac:(unfold w_sp0, PM_FRAME; lia)). apply (stores_in_agree _ _ _ _ ST3 ltac:(intros b0 Hb0; exact Hb0)). unfold zwin in *. lia. }
        apply (CONT A5 R5 M5 model5 b' cap').
        + split; [exact X5|]. split; [exact Htr|]. split; [exact BUD5|]. split; [exact (oregs_kept w Rx R5 ORx KEPT5)|].
          split; [eapply (PmBody1S1.loop_mem_frame w M2 M5); [exact LM2 | lia | lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]|].
          split; [eapply (PmBody1S1.ictx_agree w M2 M5); [exact IC2 | lia | lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]|].
          split; [eapply (ifr_agree w M2 M5); [exact FR2 | lia | lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]|].
          cbn [set_v3 c_icount c_endian c_v3 t3b fst snd]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|].
          split; [exact MAC|]. apply Forall_app. split; [exact V3R|]. constructor; [unfold OT_VARIABLE_ID; lia | constructor].
        + intros r' Hr'. rewrite (KEPT5 r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GKx. exact Hr'.
        + eapply (PmBody1S1.cellw_frame M2 M5); [exact C686_2 | lia | cbn; lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]].
        + eapply fld_agree; [lia | cbn; lia | exact Fd | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]. }

    pm_seed R4 w c [Z_to_bv 64 r; Z_to_bv 64 (if b then 1 else 0); Z_to_bv 64 (d mod 2 ^ 64)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (10%bv, EVar 40)] R4. seedHK HK w A M2 model c E X2.
    apply (know_more E M2 [KRange (EVar 40) (if b then 1 else 0) (if b then 1 else 0); KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0);
                            KWord (SA (EVar 32) 752) (N.to_nat 8) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply krange_var; [evs; reflexivity | destruct b; lia | destruct b; lia].
         - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X2) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [unfold CRep.fld in *; rewrite <- (LibMaskBits.Z_to_bv_mod64 d); exact Fd | cbn; pose proof (Z.mod_pos_bound d (2 ^ 64)); lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    destruct (Z.eq_dec r 0) as [Hr0 | Hrn].
    -
      subst r. specialize (Hhnd eq_refl). cbn beta in Hhnd.
      apply (know_more E M2 [KRange (EVar 39) 0 0]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }

      assert (TAIL : forall A' M' model' c' R' (pre : list Z),
                OBASE w I A' M' model' c' R' -> (forall r', In r' [18; 21; 23; 25]%bv -> getr R' r' = getr R2 r') ->
                cellw SEGS M' (w_sp w + 686) 2 1 -> fld SEGS M' (w_sp w + 752) 8 d ->
                c_widx c' = c_widx c -> c_v1 c' = c_v1 c -> c_v2 c' = c_v2 c -> PmLoopS1.nodes c' = PmLoopS1.nodes c ->
                t3b (c_v3 c') = t3b (c_v3 c) ++ pre -> seed_free pre -> Zlen pre <= 1 ->
                c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c -> ~ In OT_RESULT_ID pre ->
                srealizes SEGS (cfg fx R' 0x67804 M' model') K).
      { intros A' M' model' c' R' pre OB' GK' C686' Fd' Ewidx Ev1 Ev2 Enodes Epre SFpre Hpre Em1c Em2c Em3c NRpre.
        pose proof OB' as OB''. destruct OB'' as (X' & Htr' & BUD' & OR' & LM' & IC' & FR' & _). pose proof (x_ms X') as MS'.
        pose proof OR' as OR''. destruct OR'' as (Ysp & Ygp & Ytp & Ys0 & _).
        pose (E' := Eseed R' (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                              Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c') :: Z_to_bv 64 (c_widx c') :: [Z_to_bv 64 (d mod 2 ^ 64)])).
        seedHR HR' E' [(2%bv, EVar 32); (8%bv, EVar 33)] R'. seedHK HK' w A' M' model' c' E' X'.
        apply (know_more E' M' [KWord (SA (EVar 32) 752) (N.to_nat 8) (EVar 39)]) in HK'.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             eapply kword_var; [eapply fld_cellw; [unfold CRep.fld in *; rewrite <- (LibMaskBits.Z_to_bv_mod64 d); exact Fd' | cbn; pose proof (Z.mod_pos_bound d (2 ^ 64)); lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
        xruns HR' HK' 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R8.
        rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [18; 21; 23; 25]%bv HRn eq_refl) as GK8.
        clear HRn HR' HK'. fixregs. pose proof (oregs_glue w R' R8 OR' GS G2 G3 G4 G8 (or_introl G9)) as OR8. clear GS G9.
        rewrite <- (LibMaskBits.Z_to_bv_mod64 d) in G10.
        eapply (pm_edesc_operands w A' M' model' c' fx R8 _ K X' (ex_intro _ d (ex_intro _ ext (ex_intro _ wv (conj Hhnd G10)))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
        intros R9 KEPT POST. destruct (POST d ext wv Hhnd G10) as (p & l & Hg & RS & Hp4 & Qa0' & Qa1').
        keptQ KEPT G2 Qsp9. keptQ KEPT G8 Qs09. keptQ KEPT G3 Qgp9. keptQ KEPT G4 Qtp9.
        pose proof (oregs_kept w R8 R9 OR8 KEPT) as OR9.
        assert (GK9 : forall r', In r' [18; 21; 23; 25]%bv -> getr R9 r' = getr R2 r').
        { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). rewrite (GK8 r' Hr'). apply GK'. exact Hr'. }
        clear KEPT POST GK8 OR8 G1 G2 G3 G4 G8 G10.
        pose proof (go_len_ext G GOK ext wv l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.

        try clear E'. pose (E' := Eseed R9 (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                                        Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c') :: Z_to_bv 64 (c_widx c') :: [Z_to_bv 64 p; Z_to_bv 64 (Zlen l)])).
        seedHR HR' E' [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (11%bv, EVar 40)] R9. seedHK HK' w A' M' model' c' E' X'.
        xruns HR' HK' 100%nat (0x670b0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R10.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [18; 21; 23; 25]%bv HRn eq_refl) as GK10.
        clear HRn HR' HK'. fixregs. pose proof (oregs_glue w R9 R10 OR9 GS G2 G3 G4 G8 (or_introl G9)) as OR10. clear GS G9.
        assert (OB10 : OBASE w I A' M' model' c' R10).
        { split; [exact X'|]. split; [exact Htr'|]. split; [exact BUD'|]. split; [exact OR10|]. split; [exact LM'|]. split; [exact IC'|]. split; [exact FR'|].
          destruct OB' as (_ & _ & _ & _ & _ & _ & _ & REST). exact REST. }
        eapply (pm_span_push w c0 K fx I A' M' model' c' R10 p l PS OB10 G10 G11 RS Hp4 (go_ext_zw G GOK ext wv l Hg)).
        + apply Forall_forall. intros x Hx. eapply (go_range G GOK l x); [right; right; exists ext, wv; exact Hg | exact Hx].
        + exact Hll.
        + rewrite Epre, Zlen_app. unfold V3MAX in *. lia.
        + intros A'' M'' model'' R'' b'' cap'' l' El' SF' Hlen' Hr' OB'' GK'' AG''.
          eapply (PK A'' M'' model'' _ R'' 1 (pre ++ l') OB'').
          * rewrite (GK'' 21%bv), (GK10 21%bv), (GK9 21%bv), (GK2 21%bv) by (clear; inl). exact Q21.
          * rewrite (GK'' 23%bv), (GK10 23%bv), (GK9 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
          * rewrite (GK'' 25%bv), (GK10 25%bv), (GK9 25%bv), (GK2 25%bv) by (clear; inl). exact Q25.
          * eapply (PmBody1S1.cellw_frame M' M''); [exact C686' | lia | cbn; lia | eapply agree_on_weaken; [exact AG'' | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
          * left. lia.
          * cbn [set_v3 c_widx]. exact Ewidx. * cbn [set_v3 c_v1]. exact Ev1. * cbn [set_v3 c_v2]. exact Ev2.
          * unfold PmLoopS1.nodes in *. cbn [set_v3 c_m1 c_m2 c_m3]. lia.
          * cbn [set_v3 c_v3 t3b fst snd]. rewrite El', Epre, <- app_assoc. reflexivity.
          * apply seed_free_app; [exact SFpre | exact SF'].
          * rewrite Zlen_app. lia.
          * right. exact Ht36.
          * cbn [set_v3 c_m2]. exact Em2c.
          * left. cbn [set_v3 c_m1]. exact Em1c.
          * left. cbn [set_v3 c_m3]. exact Em3c.
          * intros Hin3. apply in_app_or in Hin3. destruct Hin3 as [Hin3|Hin3]; [exact (NRpre Hin3) | exact (notrid_ext CL _ _ _ _ _ Hg El' Hin3)]. }
      destruct b.
      +
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [18; 21; 23; 25]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
        rewrite w_add in G11 by lia. replace (Z_to_bv 5 (Z.of_N 20)) with (20%bv : reg) in G10 by (apply bv_eq; reflexivity). rewrite Qs44 in G10.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
        apply (PB52 R5 M3 0x67804 OR5 ltac:(intros r' Hr'; rewrite (GK5 r' Hr'); apply GK4; exact Hr') G1 ltac:(right; reflexivity) G10 G11 ltac:(unfold M3; stin) ltac:(unfold M3; rdback)).
        intros A5 R6 M5 model5 b' cap' OB5 GK6 C686_5 Fd5.
        apply (TAIL A5 M5 model5 _ R6 [OT_VARIABLE_ID] OB5 GK6 C686_5 Fd5); try reflexivity.
        all: first [exact seed_free_52 | rewrite Zlen_cons, Zlen_nil; lia | exact notrid_varid].
      +
        xruns HR HK 100%nat (0x67804 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [18; 21; 23; 25]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
        apply (TAIL A M2 model c R5 [] (OB2 R5 OR5) ltac:(intros r' Hr'; rewrite (GK5 r' Hr'); apply GK4; exact Hr') C686_2 Fd); try reflexivity.
        all: first [rewrite app_nil_r; reflexivity | exact PmZw.seed_free_nil | rewrite Zlen_nil; lia | intros []].
    -
      apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      destruct b.
      +
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [18; 21; 23; 25]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
        rewrite w_add in G11 by lia. replace (Z_to_bv 5 (Z.of_N 20)) with (20%bv : reg) in G10 by (apply bv_eq; reflexivity). rewrite Qs44 in G10.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
        apply (PB52 R5 M3 0x67570 OR5 ltac:(intros r' Hr'; rewrite (GK5 r' Hr'); apply GK4; exact Hr') G1 ltac:(left; reflexivity) G10 G11 ltac:(unfold M3; stin) ltac:(unfold M3; rdback)).
        clear G1 G2 G3 G4 G8 G10 G11. intros A5 R6 M5 model5 b' cap' OB5 GK6 C686_5 Fd5.
        pose proof OB5 as OB5'. destruct OB5' as (X5 & _ & _ & OR6 & _). pose proof (x_ms X5) as MS5.
        pose proof OR6 as OR6'. destruct OR6' as (Ysp & Ygp & Ytp & Ys0 & _).

        try clear E. pose (E := Eseed R6 (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                                     Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c) :: Z_to_bv 64 (c_widx c) :: (@nil word))).
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6.
        assert (HK : know_ok SEGS E M5 pm_kn).
        { apply (pmx_know w A5 M5 model5 (set_v3 c (b', t3b (c_v3 c) ++ [OT_VARIABLE_ID], cap')) E X5); evs; reflexivity. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R7.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [18; 21; 23; 25]%bv HRn eq_refl) as GK7.
        clear HRn HR HK. fixregs. pose proof (oregs_glue w R6 R7 OR6 GS G2 G3 G4 G8 (or_introl G9)) as OR7. clear GS G9.
        eapply (PK A5 M5 model5 _ R7 1 [OT_VARIABLE_ID]).
        * destruct OB5 as (_ & Htr5 & BUD5 & _ & REST). split; [exact X5|]. split; [exact Htr5|]. split; [exact BUD5|]. split; [exact OR7 | exact REST].
        * rewrite (GK7 21%bv), (GK6 21%bv), (GK2 21%bv) by (clear; inl). exact Q21.
        * rewrite (GK7 23%bv), (GK6 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
        * rewrite (GK7 25%bv), (GK6 25%bv), (GK2 25%bv) by (clear; inl). exact Q25.
        * exact C686_5.
        * left. lia.
        * reflexivity. * reflexivity. * reflexivity.
        * unfold PmLoopS1.nodes. cbn [set_v3 c_m1 c_m2 c_m3]. lia.
        * cbn [set_v3 c_v3 t3b fst snd]. reflexivity.
        * exact seed_free_52.
        * rewrite Zlen_cons, Zlen_nil. lia.
        * right. exact Ht36.
        * reflexivity. * left; reflexivity. * left; reflexivity. * exact notrid_varid.
      +
        xruns HR HK 100%nat (0x67964 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
        pose proof (syms_id_sound _ _ _ _ [18]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs. rewrite Qgp4 in G3. rewrite Qtp4 in G4.
        assert (G18 : getr R5 18%bv = sxw wv) by (rewrite (GK5 18%bv), (GK4 18%bv) by (clear; inl); exact Q18b).
        exact (ext_diag w c0 K fx A M2 model c R5 wv PS FZ CK X2 Htr BUD G2 G3 G4 G8 G18 Hword).
  Qed.
End PM.
End PmArm_ExtS1.

Module PmArm_LitS1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4S1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation nodes := (PmLoopS1.nodes).
  #[local] Notation macct := (PmLoopS1.macct).
  #[local] Notation GOK := (cl_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cl_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cl_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsS1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsS1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsS1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsS1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).

  Theorem arm_LITINT_S1 : forall t, (t = 6 \/ t = 45) -> arm_stmt t 0x67420.
  Proof using AC MI ST G idesc.
    intros t Ht w c0 K fx I A M model c R wv PS FZ IP HAE PK CK AACC. specialize (PK fx FZ). specialize (CK fx FZ).
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Htr31 & Hword & Q18 & Q21 & Q22 & Q23 & Q25 & PO & C680).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct PO as (_ & C686 & _).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK1.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 688) (w_sp w + 700)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 688) (w_sp w + 700)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 688) (w_sp w + 700) a) M M1).
    { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
    assert (LM1 : loop_mem w M1) by (eapply (PmBody1S1.loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (C686' : cellw SEGS M1 (w_sp w + 686) 2 1).
    { eapply (PmBody1S1.cellw_frame M M1); [exact C686 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
    pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.
    eapply (PK A M1 model c R1 1 []).
    - split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
    - rewrite (GK1 21%bv) by (clear; inl). exact Q21.
    - rewrite (GK1 23%bv) by (clear; inl). exact Q23.
    - rewrite (GK1 25%bv) by (clear; inl). exact Q25.
    - exact C686'.
    - left; lia.
    - reflexivity. - reflexivity. - reflexivity.
    - change (Z.min 1 1) with 1. lia.
    - rewrite app_nil_r. reflexivity. - exact PmZw.seed_free_nil. - rewrite PmZw.Zlen_nil. lia. - left; reflexivity.
      - reflexivity. - left; reflexivity. - left; reflexivity. - intros [].
  Qed.

  Theorem arm_LITFLOAT_S1 : forall t, t = 10 -> arm_stmt t 0x67580.
  Proof using AC MI ST G idesc.
    intros t Ht w c0 K fx I A M model c R wv PS FZ IP HAE PK CK AACC. specialize (PK fx FZ). specialize (CK fx FZ).
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Htr31 & Hword & Q18 & Q21 & Q22 & Q23 & Q25 & PO & C680).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct PO as (_ & C686 & _).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK1.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 688) (w_sp w + 700)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 688) (w_sp w + 700)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 688) (w_sp w + 700) a) M M1).
    { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
    assert (LM1 : loop_mem w M1) by (eapply (PmBody1S1.loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (C686' : cellw SEGS M1 (w_sp w + 686) 2 1).
    { eapply (PmBody1S1.cellw_frame M M1); [exact C686 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
    pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.
    eapply (PK A M1 model c R1 1 []).
    - split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
    - rewrite (GK1 21%bv) by (clear; inl). exact Q21.
    - rewrite (GK1 23%bv) by (clear; inl). exact Q23.
    - rewrite (GK1 25%bv) by (clear; inl). exact Q25.
    - exact C686'.
    - left; lia.
    - reflexivity. - reflexivity. - reflexivity.
    - change (Z.min 1 1) with 1. lia.
    - rewrite app_nil_r. reflexivity. - exact PmZw.seed_free_nil. - rewrite PmZw.Zlen_nil. lia. - left; reflexivity.
      - reflexivity. - left; reflexivity. - left; reflexivity. - intros [].
  Qed.
End PM.
End PmArm_LitS1.

Module PmArm_TyScDfS1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4S1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation nodes := (PmLoopS1.nodes).
  #[local] Notation macct := (PmLoopS1.macct).
  #[local] Notation GOK := (cl_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cl_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cl_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsS1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsS1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsS1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsS1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).
  Definition pm_operand_type_str := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_operand_type_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma w2le4_sxw : forall v, word_to_le_bytes 4 (sxw v) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v. unfold sxw. change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N. apply word_to_le_bytes_swrap. cbn; lia. Qed.

  Lemma typeid_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x67810 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagE w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | split; [exact G13 | lia] |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x12e0d 19 19 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M2 (w_sp w + 272 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R2cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R2cd (-10) _ _ B2 []);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  Lemma scope_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (t : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 21%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 ->
    srealizes SEGS (cfg fx R 0x6734c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R t PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 Q21 Ht.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (21%bv) G21.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q21 in *. clear Q21. rename G21 into Q21.
    eapply (pm_pdiag0 w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | reflexivity |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q21 Q21_. clear Q21. rename Q21_ into Q21.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (21%bv, EVar 39)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (21%bv) G21.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q21 in *. clear Q21. rename G21 into Q21.
    assert (Hlit2 : 0 <= t < 2 ^ 32) by lia.
    eapply (pm_operand_type_str w A1 M1 model1 (set_tr c (B1 ++ [])) fx R2 _ K X1 (ex_intro _ t (conj Hlit2 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R2n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R2n w (set_tr c (B1 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2n. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (21%bv) G21.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rename G21 into Q21p.
    eapply (pm_strlen w A1 M1 model1 (set_tr c (B1 ++ [])) fx R3 _ K X1 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q21p Q21p_. clear Q21p. rename Q21p_ into Q21p.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R3s w (set_tr c (B1 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (21%bv, EVar 40)] R3s. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R4 (-4) _ pnm nnm nnm _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pm_seed R4c w (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A4 M4 model4 (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) R5 (-4) _ 0x10c04 5 5 _ B4 []);
      [exact PS | exact X4 | reflexivity | exact BUD4 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS4 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS5) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M5 (w_sp w + 272 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R5cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) R5cd (-4) _ _ B5 []);
      [exact PS | exact X5 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD5 | rewrite Zlength_nil; lia | exact DS5 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  Lemma default_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (t : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 21%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 ->
    srealizes SEGS (cfg fx R 0x676b4 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R t PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 Q21 Ht.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (21%bv) G21.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q21 in *. clear Q21. rename G21 into Q21.
    eapply (pm_pdiag0 w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | reflexivity |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q21 Q21_. clear Q21. rename Q21_ into Q21.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (21%bv) G21.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q21 in *. clear Q21. rename G21 into Q21.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x14455 40 40 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q21 Q21_. clear Q21. rename Q21_ into Q21.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (21%bv, EVar 39)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (21%bv) G21.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q21 in *. clear Q21. rename G21 into Q21.
    eapply (pm_put_int w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (t) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite Z.mod_small by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS3) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M3 (w_sp w + 272 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R3cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R3cd (-4) _ _ B3 []);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | rewrite Zlength_nil; lia | exact DS3 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  #[local] Ltac arm_intro :=
    intros w c0 K fx I A M model c R wv PS FZ IP HAE PK CK AACC; specialize (PK fx FZ); specialize (CK fx FZ);
    pose proof (AE_facts w I A M model c R _ wv IP HAE) as (_ & _ & Hoff & V3B & _ & _);
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q18 & Q21 & Q22 & Q23 & Q25 & PO & C680);
    pose proof OB as OB'; destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R);
    pose proof (x_geo X) as GEO; pose proof ac_bounds_lit as Hcv; pose proof (x_ms X) as MS;
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw); unfold w_sp0, PM_FRAME, PARSER_SIZE in *;
    pose proof OR as OR'; destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8);
    destruct PO as (_ & C686 & _).

  Theorem arm_TYPEID_S1 : forall t, t = 2 -> arm_stmt t 0x67574.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht. arm_intro.
    assert (Q18' : getr R 18%bv = sxw wv) by (rewrite Q18; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q18z : getr R 18%bv = Z_to_bv 64 0) by (rewrite Q18', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, ELit 0)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x67810 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      exact (typeid_diag w c0 K fx A M model c R1 PS FZ CK X Htr BUD G2 G3 G4 G8).
    -
      pm_seed R w c [sxw wv].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_eq_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK1.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      rewrite w2le4_sxw.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 240) (w_sp w + 244)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 240) (w_sp w + 244)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 240) (w_sp w + 244) a) M M1).
      { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
      assert (LM1 : loop_mem w M1) by (eapply (PmBody1S1.loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (FR1 : ifr w M1) by (unfold M1; apply ifr_store4; [exact FR | right; left; reflexivity | lia | lia | lia]).
      assert (C686' : cellw SEGS M1 (w_sp w + 686) 2 1).
      { eapply (PmBody1S1.cellw_frame M M1); [exact C686 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.
      eapply (PK A M1 model c R1 1 []).
      + split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
        split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
      + rewrite (GK1 21%bv) by (clear; inl). exact Q21.
      + rewrite (GK1 23%bv) by (clear; inl). exact Q23.
      + rewrite (GK1 25%bv) by (clear; inl). exact Q25.
      + exact C686'.
      + left; lia.
      + reflexivity. + reflexivity. + reflexivity.
      + change (Z.min 1 1) with 1. lia.
      + rewrite app_nil_r. reflexivity. + exact PmZw.seed_free_nil. + rewrite PmZw.Zlen_nil. lia. + left; reflexivity.
      + reflexivity. + left; reflexivity. + left; reflexivity. + intros [].
  Qed.

  Theorem arm_SCOPE_S1 : forall t, (t = 4 \/ t = 5) -> arm_stmt t 0x67348.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht. arm_intro.
    assert (Q18' : getr R 18%bv = sxw wv) by (rewrite Q18; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q18z : getr R 18%bv = Z_to_bv 64 0) by (rewrite Q18', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c [Z_to_bv 64 t].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, ELit 0); (21%bv, EVar 39)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x6734c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (21%bv) G21.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      exact (scope_diag w c0 K fx A M model c R1 t PS FZ CK X Htr BUD G2 G3 G4 G8 G21 Ht31).
    -
      pm_seed R w c [sxw wv].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_ne_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK1.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      eapply (PK A M model c R1 1 []).
      + split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM|]. split; [exact IC|]. split; [exact FR|].
        split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
      + rewrite (GK1 21%bv) by (clear; inl). exact Q21.
      + rewrite (GK1 23%bv) by (clear; inl). exact Q23.
      + rewrite (GK1 25%bv) by (clear; inl). exact Q25.
      + exact C686.
      + left; lia.
      + reflexivity. + reflexivity. + reflexivity.
      + change (Z.min 1 1) with 1. lia.
      + rewrite app_nil_r. reflexivity. + exact PmZw.seed_free_nil. + rewrite PmZw.Zlen_nil. lia. + left; reflexivity.
      + reflexivity. + left; reflexivity. + left; reflexivity. + intros [].
  Qed.

  Theorem arm_DEFAULT_S1 : forall t, arm_stmt t 0x676b4.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t. arm_intro.
    exact (default_diag w c0 K fx A M model c R t PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 Q21 Ht31).
  Qed.
End PM.
End PmArm_TyScDfS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_EnumS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_RidS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_StrLibS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_StrS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_TylS1.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts3 S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmBody2S1 PmZw PmOLoopS1 PmStep4S1 PmStep5S1 PmExitDiagS1 PmOHeadS1 PmExitS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrDiagS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmDispatchS1 PmArm_MaskS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_IdS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_SpecS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_ExtS1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_LitS1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_TyScDfS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_EnumS1 PmArm_RidS1 PmArm_StrLibS1 PmArm_StrS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b20_69b24. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b5c_69b60. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmSetNumS1 PmArm_TylS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
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
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).
  #[local] Notation pm_X1 := (PmOLoopS1.pm_X1 CL).
  #[local] Notation pm_opnd_pb := (PmOLoopS1.pm_opnd_pb CL).
  #[local] Notation pm_copy_loop := (PmOLoopS1.pm_copy_loop CL).
  #[local] Notation pm_push_tail := (PmOLoopS1.pm_push_tail CL).
  #[local] Notation pm_v3_pb := (PmStep4S1.pm_v3_pb CL).
  #[local] Notation pm_oty_pb := (PmStep4S1.pm_oty_pb CL).
  #[local] Notation pm_find_m1 := (PmStep4S1.pm_find_m1 CL).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).
  #[local] Notation pm_spec_lookup := (PmStep4S1.pm_spec_lookup CL).
  #[local] Notation pm_B2 := (PmBody2S1.pm_B2 CL).
  #[local] Notation pm_B1 := (PmBody1S1.pm_B1 CL).
  #[local] Notation pm_h5 := (PmStep5S1.pm_h5 CL).
  #[local] Notation pm_D7 := (PmExitDiagS1.pm_D7 CL).
  #[local] Notation pm_D8 := (PmExitDiagS1.pm_D8 CL).
  #[local] Notation pm_D9 := (PmExitDiagS1.pm_D9 CL).
  #[local] Notation pm_oloop := (PmOHeadS1.pm_oloop CL).
  #[local] Notation pm_xexit := (PmExitS1.pm_xexit CL).
  #[local] Notation pm_main := (PmLoopS1.pm_main CL).
  #[local] Notation pm_loop := (PmLoopS1.pm_loop CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OLI := (PmODefsS1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation iacc := (PmODefsS1.iacc (generates_type:=generates_type)).
  #[local] Notation GOK := (cl_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma bfilter_app : forall (P : Z -> Prop) (H : forall x, base.Decision (P x)) (a b : list Z),
    base.filter P (a ++ b) = base.filter P a ++ base.filter P b.
  Proof using.
    intros P H a b. induction a as [|x a IH]; [rewrite bfilter_nil; reflexivity|]. cbn [app]. rewrite !bfilter_cons, IH.
    destruct (base.decide (P x)); reflexivity.
  Qed.
  Lemma push_types_nil_cons : forall z r, push_types (z :: r) [] = push_types r [] ++ (if negb (z =? OT_NONE) then [z] else []).
  Proof using.
    intros z r. unfold push_types. cbn [app rev]. rewrite bfilter_app, bfilter_cons, bfilter_nil.
    destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
      exfalso; [exact Hd | apply Hd; exact Logic.I].
  Qed.
  Lemma push_types_nil_snoc : forall r z, push_types (r ++ [z]) [] = (if negb (z =? OT_NONE) then [z] else []) ++ push_types r [].
  Proof using.
    intros r z. unfold push_types. cbn [app]. rewrite rev_app_distr. cbn [rev app]. rewrite bfilter_cons.
    destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
      exfalso; [exact Hd | apply Hd; exact Logic.I].
  Qed.

  Lemma zw_init : forall l, op_list_ok l -> zw_stack_ok (push_types l []).
  Proof using.
    intros l [SF H47]. destruct l as [|z r _] using rev_ind.
    - change (push_types [] []) with (@nil Z ++ @nil Z). apply zw_stack_ok_intro; [exact seed_free_nil | left; reflexivity].
    - rewrite removelast_last in SF. rewrite push_types_nil_snoc.
      destruct (push_types_split r []) as (top & Etop & _ & Hin). cbn [app] in Etop. rewrite Etop.
      assert (SFt : seed_free top) by (intros t Ht; exact (SF t (Hin t Ht))).
      destruct (negb (z =? OT_NONE)) eqn:Ez.
      + destruct (zw_seed z) eqn:Es.
        * change ([z] ++ top) with ([z] ++ top). apply zw_stack_ok_intro; [exact SFt|].
          unfold zw_seed, zw_type in Es. unfold_OT.
          pose proof (H47 z ltac:(apply in_app_iff; right; left; reflexivity)) as Hz47. unfold_OT.
          destruct (Z.eqb_spec z 9); [subst; right; left; reflexivity|].
          destruct (Z.eqb_spec z 47); [exfalso; exact (Hz47 ltac:(assumption))|].
          destruct (Z.eqb_spec z 54); [subst; right; right; right; left; reflexivity|].
          destruct (Z.eqb_spec z 8); [subst; right; right; left; reflexivity|].
          cbn in Es. discriminate.
        * change ([z] ++ top) with ([] ++ ([z] ++ top)). apply zw_stack_ok_intro; [| left; reflexivity].
          intros t [<-|Ht]; [exact Es | exact (SFt t Ht)].
      + cbn [app]. change top with ([] ++ top). apply zw_stack_ok_intro; [exact SFt | left; reflexivity].
  Qed.

  Lemma pm_body : forall (w : pmw MI ST) c0 K (fx : FPState),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> (forall t, arm_stmt t (arm_pc t)) -> body_stmt w c0 K fx.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx PS FZ ARMS A M model c R HLI Hlt Qa0 LK.
    pose proof HLI as HLI'. destruct HLI' as (X & Htr & BUD & LR & LM & Hw5 & He2 & HwN & ACC & MACC & LACC).
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    eapply (pm_B1 w c0 K fx A M model c R PS FZ HLI Hlt Qa0).
    intros A1 M1 model1 c1 R1 fw iwc op d X1 Htr1 BUD1 LR1 LM1 IZ1 IC1 Eiwc Eop Hiwc Rfw [l Hg] Hdesc Ewidx Eic Eend Erc Ev1 Ev2 Em1 Em2 Em3 Ev3 Ev1c.
    eapply (pm_B2 w c0 K fx A1 M1 model1 c1 R1 (c_widx c) fw iwc op d l PS X1 Htr1 BUD1 LR1 LM1 IZ1 IC1 Hg Hdesc).
    intros A2 M2 model2 R2 b' cap' X2 BUD2 LR2 LM2 IZ2 IC2.
    destruct (push_types_split l []) as (xs & Exs & Hxl & Hin). cbn [app] in Exs. rewrite Exs in X2, BUD2.
    set (I := ICTX (c_widx c) fw iwc op d l).
    set (c2 := set_v3 c1 (b', xs, cap')) in *.
    assert (IP : ipure I).
    { unfold PmODefsS1.ipure. cbn [I i_io i_fw i_iwc i_op i_d i_l]. repeat split; first [assumption | lia]. }
    pose proof (ipure_ranges I IP) as (Riwc & Rop). cbn [I i_iwc i_op] in Riwc, Rop.
    pose proof (go_op_zw G GOK op l Hg) as OLOK.
    pose proof (go_len_op G GOK op l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.
    pose proof (cl_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as Hml.
    assert (Hrange : Forall (fun x => 0 <= x < 2 ^ 31) l).
    { apply Forall_forall. intros x Hx. eapply (go_range G GOK l x); [left; exists op; exact Hg | exact Hx]. }
    assert (FRxs : Forall (fun x => 0 <= x < 2 ^ 31) xs).
    { apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) Hrange x (Hin x Hx)). }
    pose proof (Zlen_nonneg xs) as Hxs0. pose proof (zw_next_range xs) as Hzn.
    assert (LK' : LOOPK w K (i_io I)) by (unfold LOOPK; cbn [I i_io]; exact LK).
    apply (pm_oloop w c0 K I PS IP ARMS
             (fun fx3 A3 M3 model3 c3 R3 FZ3 HOLI Hle Q22 Q21 Q10 Q11 Q13 Q12 => pm_xexit w c0 K fx3 I A3 M3 model3 c3 R3 PS FZ3 IP HOLI Hle Q22 Q21 Q10 Q11 Q13 Q12 LK')
             (fun fx3 A3 M3 model3 c3 R3 FZ3 HOLI Hlt3 Hnil Q22 Q21 Q10 => pm_D7 w c0 K fx3 I A3 M3 model3 c3 R3 PS FZ3 IP HOLI Hlt3 Hnil Q22 Q21 Q10)
             fx A2 M2 model2 c2 R2 FZ).

    unfold PmODefsS1.OLI, OBASE, omeas, PmLoopS1.nodes, PmLoopS1.macct, PmLoopS1.lacc in *.
    cbn [I i_io i_fw i_iwc i_op i_d i_l c2 set_v3 c_widx c_icount c_endian c_reqconv c_tr c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 t3a t3b t3c fst snd] in *.
    rewrite ?Ewidx, ?Eic, ?Eend, ?Erc, ?Ev1, ?Ev2, ?Em1, ?Em2, ?Em3 in *.
    split.
    { split; [exact X2|]. split; [exact Htr1|]. split; [exact BUD2|]. split; [exact (loop_regs_oregs w R2 LR2)|]. split; [exact LM2|].
      split; [exact IC2|]. split; [exact (izero_ifr w M2 IZ2)|]. split; [lia|]. split; [lia|]. split; [exact HwN|]. split; [exact MACC | exact FRxs]. }
    split; [lia|]. split; [lia|].
    split. { change (Zlen [fw]) with 1 in *. replace (c_widx c + iwc - (c_widx c + 1)) with (iwc - 1) by lia. rewrite Z.max_r by lia. lia. }
    split. { change (Zlen [fw]) with 1. lia. }
    split; [lia|].
    split; [rewrite <- Exs; exact (zw_init l OLOK)|].
    split.
    {   destruct (Z.eq_dec op OP_TYPE_INT) as [EI|NI]; [| destruct (Z.eq_dec op OP_TYPE_FLOAT) as [EF|NF]; [| exact (nty_other op xs _ NI NF)]].
      - rewrite EI in Hg |- *. rewrite (go_typeint G GOK l Hg) in Exs. rewrite <- Exs. apply nty_init_int. lia.
      - rewrite EF in Hg |- *. rewrite (go_typefloat G GOK l Hg) in Exs. rewrite <- Exs. apply nty_init_float. lia. }

    unfold PmODefsS1.iacc. cbn [I i_io i_op c2 set_v3 c_widx c_m1 c_m2 c_m3 c_v3 t3b t3c fst snd]. rewrite ?Em1, ?Em2, ?Em3, ?Ewidx.
    destruct LACC as (L1 & L2 & L3).
    split.
    { exists 0. split; [lia|]. split; [lia|]. split; [intros; lia|].
      pose proof (ridc_push_types_nil l) as RP1. rewrite Exs in RP1.
      pose proof (ridc_le1_of_count l ((proj1 (cl_rid1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)) op l Hg)). lia. }
    split; [lia|].
    split.
    { exists 0. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|].
      intros EI. left. split; [reflexivity|]. rewrite EI in Hg. rewrite (cl_import _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) in Hg.
      injection Hg. intros <-. rewrite <- Exs. reflexivity. }
    intros Hgt. right. destruct ((cl_gt_rid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) op l Hgt Hg) as (r & ->).
    exists (push_types r []). rewrite <- Exs, push_types_nil_cons. reflexivity.
  Qed.

  Theorem parse_module_S1_of_arms : (forall t, arm_stmt t (arm_pc t)) -> parse_module_stmt SEGS Ly.L MI ST kcS1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL. intros ARMS. apply pm_main. intros w c0 K fx PS FZ. exact (pm_body w c0 K fx PS FZ ARMS). Qed.

  Lemma arms_all : forall t, arm_stmt t (arm_pc t).
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t. pose proof (PmArm_RidS1.arm_RESULTID_S1 CL) as RID. pose proof (PmArm_StrS1.arm_LITSTR_S1 CL) as LS. unfold OT_LITERAL_STRING in LS.
    pose proof (PmArm_TylS1.arm_TYPEDLIT_S1 CL) as TL. unfold OT_TYPED_LITERAL_NUMBER, OT_OPTIONAL_TYPED_LITERAL_INTEGER in TL. unfold arm_pc.
    destruct (Z.lt_ge_cases t 1) as [H0|H1].
    { replace ((1 <=? t) && (t <=? 107))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). apply (PmArm_TyScDfS1.arm_DEFAULT_S1 CL). }
    destruct (Z.lt_ge_cases 107 t) as [H2|H3].
    { replace ((1 <=? t) && (t <=? 107))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia). apply (PmArm_TyScDfS1.arm_DEFAULT_S1 CL). }
    pose proof (PmDispatchS1.In_range_enum t 1 107 ltac:(lia)) as HIn. vm_compute in HIn.
    repeat match type of HIn with
           | _ \/ _ => destruct HIn as [HIn|HIn];
               [subst t; lazymatch goal with |- arm_stmt ?tt ?pc => let v := eval vm_compute in pc in change pc with v end;
                first [ exact RID | apply TL; lia | apply LS; lia
                      | apply (PmArm_IdS1.arm_ID_S1 CL); lia | apply PmArm_LitS1.arm_LITINT_S1; lia | apply PmArm_LitS1.arm_LITFLOAT_S1; reflexivity
                      | apply (PmArm_TyScDfS1.arm_TYPEID_S1 CL); reflexivity | apply (PmArm_TyScDfS1.arm_SCOPE_S1 CL); lia
                      | apply (PmArm_EnumS1.arm_SRCLANG_S1 CL); reflexivity | exact (PmArm_ExtS1.arm_EXTNUM_S1 CL) | exact (PmArm_SpecS1.arm_SPECOP_S1 CL)
                      | apply (PmArm_MaskS1.arm_MASK_S1 CL); (first [solve [clear; cbn; tauto] | cbn; tauto]) | apply (PmArm_EnumS1.arm_ENUM_S1 CL); apply PmArm_EnumS1.in_enum_types; reflexivity
                      | apply (PmArm_TyScDfS1.arm_DEFAULT_S1 CL) ] |]
           | False => destruct HIn
           end.
  Qed.

  Theorem parse_module_S1 : parse_module_stmt SEGS Ly.L MI ST kcS1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL. exact (parse_module_S1_of_arms arms_all). Qed.
End PM.
