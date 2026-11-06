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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1 HWord.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmZw PmODefsU1 PmStep4U1 PmDispatchU1 PmSetNumU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cu_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cu_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsU1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsU1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsU1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4U1.pm_find_m3 CL).
  #[local] Notation pm_find_m1 := (PmStep4U1.pm_find_m1 CL).
  #[local] Notation pm_spec_lookup := (PmStep4U1.pm_spec_lookup CL).
  #[local] Notation pm_oty_pb := (PmStep4U1.pm_oty_pb CL).
  Definition pm_is_ext_inst := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_ext_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_nonsemantic := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_nonsemantic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_operand_type_str := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_operand_type_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma w2le4_sxw : forall v, word_to_le_bytes 4 (sxw v) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v. unfold sxw. change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N. apply word_to_le_bytes_swrap. cbn; lia. Qed.
  #[local] Notation pm_set_numeric := (PmSetNumU1.pm_set_numeric CL).

  Lemma ty_diag_a : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (sel : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> cellw SEGS M (w_sp w + 280) 4 sel ->
    srealizes SEGS (cfg fx R 0x681ac M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R sel PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C280.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C280) as Hsel. cbn in Hsel.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x13e6a 30 30 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw sel].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C280. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (sel) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-4) _ 0x1063d 12 12 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS4) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M4 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R4cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R4cd (-4) _ _ B4 []);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | rewrite Zlength_nil; lia | exact DS4 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma ty_diag_b : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (sel : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> cellw SEGS M (w_sp w + 280) 4 sel ->
    srealizes SEGS (cfg fx R 0x67cb0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R sel PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C280.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C280) as Hsel. cbn in Hsel.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x13e6a 30 30 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw sel].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C280. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (sel) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-4) _ 0x123e3 23 23 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS4) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M4 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R4cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R4cd (-4) _ _ B4 []);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | rewrite Zlength_nil; lia | exact DS4 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma ty_diag_c : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (sel : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> cellw SEGS M (w_sp w + 280) 4 sel ->
    srealizes SEGS (cfg fx R 0x68400 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R sel PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C280.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C280) as Hsel. cbn in Hsel.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x13e6a 30 30 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw sel].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C280. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (sel) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in C280; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-4) _ 0x12b2f 24 24 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS4) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M4 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R4cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R4cd (-4) _ _ B4 []);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | rewrite Zlength_nil; lia | exact DS4 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma oregs_gk : forall (w : pmw MI ST) R R', oregs w R ->
    (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) -> oregs w R'.
  Proof using AC MI ST.
    intros w R R' OR GK. destruct OR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q25). unfold oregs, loop_regs.
    rewrite (GK 2%bv), (GK 3%bv), (GK 4%bv), (GK 8%bv), (GK 9%bv), (GK 18%bv), (GK 19%bv), (GK 20%bv), (GK 21%bv), (GK 25%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]).
    repeat split; assumption.
  Qed.

  Lemma sx32_eqb : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> (PrsGrammar.sx32 a =? PrsGrammar.sx32 b) = (a =? b).
  Proof using.
    intros a b Ha Hb. unfold PrsGrammar.sx32.
    destruct (Z.ltb_spec a (2 ^ 31)); destruct (Z.ltb_spec b (2 ^ 31));
      (destruct (Z.eqb_spec a b); [subst; first [reflexivity | rewrite Z.eqb_refl; reflexivity | exfalso; lia] | first [reflexivity | apply Z.eqb_neq; lia]]).
  Qed.

  Lemma pm_peek_at : forall (w : pmw MI ST) A M model c (fx : FPState) R (i ret : Z) K,
    PMX w A M model c -> c_endian c < 2 -> w_words w <> 0 ->
    getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 11%bv = Z_to_bv 64 i -> 0 <= i < w_n w ->
    getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    (forall R' (r : Z), kept R R' -> 0 <= r < 2 ^ 32 -> getr R' 10%bv = Z_to_bv 64 (PrsNeeds.sx32 r) ->
        srealizes SEGS (cfg fx R' ret M model) K) ->
    srealizes SEGS (cfg fx R 0x6a06c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w A M model c fx R i ret K X Hend Hwnz Ha0 Ha1 Hi Hra Hret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct (Gw Hwnz) as (W1 & W2 & W3 & W4 & W5). pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (x_words X) as Fw. pose proof (x_endian X) as Fe. unfold O_WORDS, O_ENDIAN in Fw, Fe.
    destruct ((cu_peek_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx R M (w_p w) i (w_words w) (c_endian c) (Z_to_bv 64 ret)
                (x_roc X) Ha0 Ha1 Fw Fe ltac:(lia) W1 W2 ltac:(lia) ltac:(lia)
                ltac:(eapply mdef_sub; [exact (x_wbuf X Hwnz) | lia | lia]) ltac:(lia) ltac:(lia)
                ltac:(apply PmSetNumU1.mod16_mod8; exact Gp16) Hra Hret)
      as (R' & MSx & KP & r & Hr & G10).
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |].
    exact (CONT R' r KP Hr G10).
  Qed.

  Theorem arm_TYPEDLIT_U1 : forall t, t = OT_TYPED_LITERAL_NUMBER \/ t = OT_OPTIONAL_TYPED_LITERAL_INTEGER -> arm_stmt t 0x67c64.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC. specialize (PK fx FZ FC). specialize (CK fx FZ FC).
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (ipure_ranges I IP) as (Riwc & Rop). destruct (Gw Hwnz) as (W1 & W2 & W3 & W4 & W5).
    assert (HSTK : PmSetNumU1.SN_D + dc_stack dcU1 <= w_STK w - PM_FRAME) by (unfold PmSetNumU1.SN_D, PM_FRAME; cbn [dc_stack dcU1]; lia).
    assert (Hzw : zw_type t = true) by (destruct Ht as [-> | ->]; reflexivity).
    pose proof (proj2 (proj2 (proj2 (proj2 MAC)))) as M2OK.
    destruct PO as (_ & C718 & _).

    assert (PUSHJ : forall A' M' model' R' (nwv : Z),
      PMX w A' M' model' c -> pm_bud (w_n w) c -> oregs w R' -> loop_mem w M' -> ictx w M' (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M' ->
      getr R' 27%bv = Z_to_bv 64 t -> getr R' 23%bv = Z_to_bv 64 (i_io I) -> getr R' 26%bv = Z_to_bv 64 (i_op I) ->
      cellw SEGS M' (w_sp w + 718) 2 nwv ->
      srealizes SEGS (cfg fx R' 0x67f60 M' model') K).
    { intros A' M' model' R' nwv X' BUD' OR' LM' IC' FR' T27 T23 T26 C718x. pose proof (proj1 C718x) as Rnw. cbn in Rnw.
      eapply (PK A' M' model' c R' nwv []); try reflexivity.
      + split; [exact X'|]. split; [exact Htr|]. split; [exact BUD'|]. split; [exact OR'|]. split; [exact LM'|]. split; [exact IC'|]. split; [exact FR'|].
        split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
      + exact T27. + exact T23. + exact T26. + exact C718x.
      + destruct (Z.eq_dec nwv 0) as [-> | Hne]; [right; split; [reflexivity | split; [exact Hzw | reflexivity]] | left; lia].
      + lia.
      + rewrite app_nil_r. reflexivity.
      + exact PmZw.seed_free_nil.
      + rewrite PmZw.Zlen_nil. lia.
      + left; reflexivity.
      + left; reflexivity.
      + left; reflexivity.
      + intros []. }

    assert (RETJ : forall (retpc : Z) A' R' M' model' (e : Z),
      retpc = 0x67e10 \/ retpc = 0x683e0 ->
      PMX w A' M' model' c -> pm_bud (w_n w) c -> oregs w R' ->
      getr R' 10%bv = sxw e -> 0 < e < 2 ^ 32 ->
      srealizes SEGS (cfg fx R' retpc M' model') K).
    { intros retpc A' R' M' model' e Hpc X' BUD' OR' Ha0 He. pose proof (x_ms X') as MS'.
      pose proof OR' as ORx. destruct ORx as (Ysp & Ygp & Ytp & Ys0 & _).
      rewrite sxw_sx32 in Ha0 by lia.
      assert (Hsx : 0 < PrsGrammar.sx32 e < 2 ^ 64) by (unfold PrsGrammar.sx32; destruct (Z.ltb_spec e (2 ^ 31)); lia).
      pm_seed R' w c [Z_to_bv 64 (PrsGrammar.sx32 e)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R'. seedHK HK w A' M' model' c E X'.
      apply (know_more E M' [KRange (EVar 39) 1 (2 ^ 64)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      destruct Hpc as [-> | ->].
      all: xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N; [split_scs; try sc_auto1 |].
      all: postrun; name_run HRn R5.
      all: rreg HRn (2%bv) T2; rreg HRn (3%bv) T3; rreg HRn (4%bv) T4; rreg HRn (8%bv) T8; rreg HRn (22%bv) T22.
      all: clear HRn HR HK; fixregs; rewrite Ygp in T3; rewrite Ytp in T4; rewrite <- sxw_sx32 in T22 by lia.
      all: exact (CK A' M' model' c R5 e X' Htr BUD' T2 T3 T4 T8 T22 He). }

    pose proof FR as FR'. destruct FR' as (ext & tid & rid & _ & _ & _ & Ctid & _). pose proof (proj1 Ctid) as Rtid. cbn in Rtid.
    destruct (Z.eq_dec (i_op I) 251) as [Hop | Hop].
    2: {
      pm_seed R w c [Z_to_bv 64 (i_op I); Z_to_bv 64 tid].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 256) (N.to_nat 4) (EVar 40)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply kword_var; [exact Ctid | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS. pose proof (syms_id_sound _ _ _ _ [22; 23; 27]%bv HRn eq_refl) as GK1. rreg HRn (26%bv) G26.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8) as OR1. clear GS.
      rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G11 by lia. rewrite ext_val_sx4 in G12 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M1 := mm) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 720) (w_sp w + 724)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 720) (w_sp w + 724)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 720) (w_sp w + 724) a) M M1).
      { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
      assert (LM1 : loop_mem w M1) by (eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      pose proof (x_ms X1) as MS1. clearbody M1. clear ST1 AG1.
      eapply (pm_set_numeric w c0 K fx A M1 model c R1 tid 0x67e10 PS X1 Htr BUD HSTK M2OK ltac:(cregs_tac G1 G2 G3 G4) G10 G11 G12 ltac:(lia)).
      intros A2 R2 M2 model2 e X2 BUD2 GK Ha0 He AG2 Hsucc.
      pose proof (oregs_gk w R1 R2 OR1 GK) as OR2.
      assert (T27 : getr R2 27%bv = Z_to_bv 64 t) by (rewrite (GK 27%bv) by (clear; cbn; tauto); rewrite (GK1 27%bv) by (clear; cbn; tauto); exact Q27).
      assert (T23 : getr R2 23%bv = Z_to_bv 64 (i_io I)) by (rewrite (GK 23%bv) by (clear; cbn; tauto); rewrite (GK1 23%bv) by (clear; cbn; tauto); exact Q23).
      assert (T26 : getr R2 26%bv = Z_to_bv 64 (i_op I)) by (rewrite (GK 26%bv) by (clear; cbn; tauto); exact G26).
      destruct (Z.eq_dec e 0) as [-> | Hne]; [| exact (RETJ 0x67e10 A2 R2 M2 model2 e (or_introl eq_refl) X2 BUD2 OR2 Ha0 ltac:(lia))].
      destruct (Hsucc eq_refl) as (nwv & nk & Cnw & Cnk & Hnk).
      replace (sxw 0) with (Z_to_bv 64 0) in Ha0 by (unfold sxw; apply bv_eq; vm_compute; reflexivity).
      pose proof OR2 as OR2'. destruct OR2' as (Ysp & Ygp & Ytp & Ys0 & _). pose proof (x_ms X2) as MS2.
      pm_seed R2 w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R2. seedHK HK w A2 M2 model2 c E X2.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) H2. rreg HRn (8%bv) H8. pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS3. pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 23; 26; 27]%bv HRn eq_refl) as GK3.
      clear HRn HR HK. fixregs.
      assert (OR3 : oregs w R3) by (eapply (oregs_glue w R2 R3 OR2 GS3); [exact H2 | apply GK3; clear; cbn; tauto | apply GK3; clear; cbn; tauto | exact H8]).
      eapply (PUSHJ A2 M2 model2 R3 nwv X2 BUD2 OR3).
      + eapply (loop_mem_frame w M1 M2); [exact LM1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      + eapply (ictx_agree w M1 M2); [exact IC1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      + eapply (ifr_agree w M1 M2); [exact FR1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      + rewrite (GK3 27%bv) by (clear; cbn; tauto). exact T27.
      + rewrite (GK3 23%bv) by (clear; cbn; tauto). exact T23.
      + rewrite (GK3 26%bv) by (clear; cbn; tauto). exact T26.
      + exact Cnw. }

    pose proof Q26 as Q26'. rewrite Hop in Q26'.
    destruct IP as (_ & _ & _ & _ & _ & _ & Hio0).
    pm_seed R w c [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, ELit 251); (23%bv, EVar 39)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
    rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS. pose proof (syms_id_sound _ _ _ _ [22; 27]%bv HRn eq_refl) as GK1. rreg HRn (23%bv) G23. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8) as OR1. clear GS.
    rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G11 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M1 := mm) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 720) (w_sp w + 724)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 720) (w_sp w + 724)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 720) (w_sp w + 724) a) M M1).
    { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
    assert (LM1 : loop_mem w M1) by (eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    pose proof (x_ms X1) as MS1. clearbody M1. clear ST1 AG1.
    eapply (pm_peek_at w A M1 model c fx R1 (i_io I + 1) _ K X1 Hend Hwnz G10 G11 ltac:(lia) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 sel KEPT Rsel Hsel.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Q2b. keptQ KEPT G8 Q8b. keptQ KEPT G23 Q23b. keptQ KEPT G26 Q26b.
    assert (Q27b : getr R2 27%bv = Z_to_bv 64 t) by (rewrite (KEPT 27%bv) by (clear; apply in_reg_list; reflexivity); rewrite (GK1 27%bv) by (clear; cbn; tauto); exact Q27).
    clear KEPT G1 G2 G3 G4 G8 G10 G11 G23 G26 GK1 OR1.

    assert (C88 : cellw SEGS M1 (w_sp w + 88) 8 (w_p w + 96)) by (eapply (loop_mem_cell w M1 88); [exact LM1 | (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia]).
    pm_seed R2 w c [Z_to_bv 64 (PrsGrammar.sx32 sel)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M1 model c E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 88) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 96))]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil. eapply kword_var; [exact C88 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS. pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 22; 23; 26; 27]%bv HRn eq_refl) as GK3.
    clear HRn HR HK. fixregs.
    assert (OR3 : oregs w R3) by (eapply (oregs_glue w R2 R3 OR2 GS); [exact G2 | apply GK3; clear; cbn; tauto | apply GK3; clear; cbn; tauto | exact G8]).
    rewrite w_add in G10 by lia. rewrite w_add in G11 by lia. rewrite ?w_add by lia. rewrite PmInstU1.w2lb4_sx32 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M2 := mm) in * end.
    assert (ST2 : stores_in (zwin (w_sp w + 280) (w_sp w + 284)) M1 M2) by (unfold M2; stin).
    assert (X2 : PMX w A M2 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 M2 model c (zwin (w_sp w + 280) (w_sp w + 284)));
        [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AG2 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 280) (w_sp w + 284) a) M1 M2).
    { eapply stores_in_agree; [exact ST2 | intros b Hb; unfold zwin in *; lia]. }
    assert (LM2 : loop_mem w M2) by (eapply (loop_mem_frame w M1 M2); [exact LM1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]).
    assert (IC2 : ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M1 M2); [exact IC1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]).
    assert (FR2 : ifr w M2) by (eapply (ifr_agree w M1 M2); [exact FR1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]).
    assert (C280 : cellw SEGS M2 (w_sp w + 280) 4 sel) by (split; [cbn; lia | unfold M2; rdback]).
    pose proof (x_ms X2) as MS2. clearbody M2. clear ST2 AG2 LM1 IC1 FR1 MS1 C88.
    pose proof OR3 as OR3'. destruct OR3' as (Ysp & Ygp & Ytp & Ys0 & _).
    eapply (pm_find_m1 w A M2 model c fx R3 (w_sp w + 280) sel 0x67c90 K X2 ltac:(unfold O_M1; exact G10) G11 C280 ltac:(lia) ltac:(lia) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4 p KEPT Hp Hfound.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4. keptQ KEPT G2 Q2d. keptQ KEPT G8 Q8d.
    assert (GK4 : forall r', In r' [22; 23; 26; 27]%bv -> getr R4 r' = getr R2 r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK3. revert Hr'; clear; cbn; intros; tauto. }
    clear KEPT G1 G2 G8 G10 G11 GK3 GS.
    assert (Q27d : getr R4 27%bv = Z_to_bv 64 t) by (rewrite (GK4 27%bv) by (clear; cbn; tauto); exact Q27b).
    assert (Q23d : getr R4 23%bv = Z_to_bv 64 (i_io I)) by (rewrite (GK4 23%bv) by (clear; cbn; tauto); exact Q23b).
    assert (Q26d : getr R4 26%bv = Z_to_bv 64 251) by (rewrite (GK4 26%bv) by (clear; cbn; tauto); exact Q26b).
    pose proof OR4 as OR4'. destruct OR4' as (Zsp & Zgp & Ztp & Zs0 & _).

    assert (NOTYPE : forall Rx, oregs w Rx -> srealizes SEGS (cfg fx Rx 0x681ac M2 model) K).
    { intros Rx ORx. destruct ORx as (Y2 & Y3 & Y4 & Y8 & _).
      exact (ty_diag_a w c0 K fx A M2 model c Rx sel PS FZ CK X2 Htr BUD Y2 Y3 Y4 Y8 C280). }
    destruct Hfound as [-> | (Hp0 & Hp47 & Hpal & v0 & Hin0 & Cv0)].
    { pm_seed R4 w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R4. seedHK HK w A M2 model c E X2.
      xruns HR HK 100%nat (0x681ac :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5. rreg HRn (2%bv) H2. rreg HRn (8%bv) H8.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS. pose proof (syms_id_sound _ _ _ _ [3; 4; 9]%bv HRn eq_refl) as GK5.
      clear HRn HR HK. fixregs.
      apply NOTYPE. eapply (oregs_glue w R4 R5 OR4 GS); [exact H2 | apply GK5; clear; cbn; tauto | apply GK5; clear; cbn; tauto | exact H8]. }
    pose proof (proj1 Cv0) as Rv0. cbn in Rv0.
    assert (Hpal8 : p mod 8 = 0) by (apply PmSetNumU1.mod16_mod8; exact Hpal).
    destruct (Z.eq_dec v0 0) as [-> | Hv0].
    { pm_seed R4 w c [Z_to_bv 64 p].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R4. seedHK HK w A M2 model c E X2.
      apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 47); KAlign (EVar 39) 8; KWord (SA (EVar 39) 20) (N.to_nat 4) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hpal8].
           - eapply kword_var; [exact Cv0 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat (0x681ac :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5. rreg HRn (2%bv) H2. rreg HRn (8%bv) H8.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS. pose proof (syms_id_sound _ _ _ _ [3; 4; 9]%bv HRn eq_refl) as GK5.
      clear HRn HR HK. fixregs.
      apply NOTYPE. eapply (oregs_glue w R4 R5 OR4 GS); [exact H2 | apply GK5; clear; cbn; tauto | apply GK5; clear; cbn; tauto | exact H8]. }

    assert (Hsx0 : 0 < PrsGrammar.sx32 v0 < 2 ^ 64) by (unfold PrsGrammar.sx32; destruct (Z.ltb_spec v0 (2 ^ 31)); lia).
    assert (Hsxs : 0 <= PrsGrammar.sx32 sel < 2 ^ 64) by (unfold PrsGrammar.sx32; destruct (Z.ltb_spec sel (2 ^ 31)); lia).
    pose proof (sx32_eqb sel v0 Rsel Rv0) as Hsxeq.
    pm_seed R4 w c [Z_to_bv 64 p; Z_to_bv 64 v0; Z_to_bv 64 sel].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R4. seedHK HK w A M2 model c E X2.
    apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 47); KAlign (EVar 39) 8; KWord (SA (EVar 39) 20) (N.to_nat 4) (EVar 40); KWord (SA (EVar 32) 280) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hpal8].
         - eapply kword_var; [exact Cv0 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C280 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    destruct (Z.eq_dec sel v0) as [Heqsv | Hnesv].
    -
      xruns HR HK 100%nat (0x67cb0 :: STOPS) (SCR [false; false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_sx4 by lia; rewrite ?br_eq, ?br_ne by lia; rewrite ?Hsxeq; bool_lia. }
      postrun. name_run HRn R5. rreg HRn (2%bv) H2. rreg HRn (8%bv) H8.
      pose proof (syms_id_sound _ _ _ _ [3; 4]%bv HRn eq_refl) as GK5.
      clear HRn HR HK. fixregs.
      exact (ty_diag_b w c0 K fx A M2 model c R5 sel PS FZ CK X2 Htr BUD H2
               ltac:(rewrite (GK5 3%bv) by (clear; cbn; tauto); exact Zgp) ltac:(rewrite (GK5 4%bv) by (clear; cbn; tauto); exact Ztp) H8 C280).
    -
      xruns HR HK 100%nat STOPS (SCR [false; true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_sx4 by lia; rewrite ?br_eq, ?br_ne by lia; rewrite ?Hsxeq; bool_lia. }
      postrun. name_run HRn R5.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS. pose proof (syms_id_sound _ _ _ _ [22; 23; 26; 27]%bv HRn eq_refl) as GK5.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8) as OR5. clear GS.
      rewrite Zgp in G3. rewrite Ztp in G4. rewrite w_add in G11 by lia. rewrite ext_val_sx4 in G12 by lia.
      eapply (pm_set_numeric w c0 K fx A M2 model c R5 v0 0x683e0 PS X2 Htr BUD HSTK M2OK ltac:(cregs_tac G1 G2 G3 G4) G10 G11 G12 ltac:(lia)).
      intros A4 R6 M4 model4 e X4 BUD4 GK Ha0 He AG4 Hsucc.
      pose proof (oregs_gk w R5 R6 OR5 GK) as OR6.
      assert (T27 : getr R6 27%bv = Z_to_bv 64 t) by (rewrite (GK 27%bv) by (clear; cbn; tauto); rewrite (GK5 27%bv) by (clear; cbn; tauto); exact Q27d).
      assert (T23 : getr R6 23%bv = Z_to_bv 64 (i_io I)) by (rewrite (GK 23%bv) by (clear; cbn; tauto); rewrite (GK5 23%bv) by (clear; cbn; tauto); exact Q23d).
      assert (T26 : getr R6 26%bv = Z_to_bv 64 (i_op I)) by (rewrite (GK 26%bv) by (clear; cbn; tauto); rewrite (GK5 26%bv) by (clear; cbn; tauto); rewrite Hop; exact Q26d).
      destruct (Z.eq_dec e 0) as [-> | Hne]; [| exact (RETJ 0x683e0 A4 R6 M4 model4 e (or_intror eq_refl) X4 BUD4 OR6 Ha0 ltac:(lia))].
      destruct (Hsucc eq_refl) as (nwv & nk & Cnw & Cnk & Hnk). pose proof (proj1 Cnk) as Rnk. cbn in Rnk.
      replace (sxw 0) with (Z_to_bv 64 0) in Ha0 by (unfold sxw; apply bv_eq; vm_compute; reflexivity).
      pose proof OR6 as OR6'. destruct OR6' as (Y6sp & Y6gp & Y6tp & Y6s0 & _). pose proof (x_ms X4) as MS4.
      assert (LM4 : loop_mem w M4) by (eapply (loop_mem_frame w M2 M4); [exact LM2 | lia | lia | eapply agree_on_weaken; [exact AG4 | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]]).
      assert (IC4 : ictx w M4 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M2 M4); [exact IC2 | lia | lia | eapply agree_on_weaken; [exact AG4 | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]]).
      assert (FR4 : ifr w M4) by (eapply (ifr_agree w M2 M4); [exact FR2 | lia | lia | eapply agree_on_weaken; [exact AG4 | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]]).
      assert (C280' : cellw SEGS M4 (w_sp w + 280) 4 sel) by (eapply (cellw_frame M2 M4); [exact C280 | lia | cbn; lia | eapply agree_on_weaken; [exact AG4 | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]]).

      assert (Hnk3 : nk = 1 \/ nk = 2 \/ nk = 3) by lia.
      pm_seed R6 w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R6. seedHK HK w A4 M4 model4 c E X4.
      apply (know_more E M4 [KWord (SA (EVar 32) 724) (N.to_nat 4) (ELit nk)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply kword_var; [exact Cnk | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      destruct Hnk3 as [-> | [-> | ->]].
      all: xruns HR HK 100%nat (0x68400 :: STOPS) (SCR [] [] []) 50%N; [split_scs; try sc_auto1 |].
      all: postrun; name_run HRn R7; rreg HRn (2%bv) H2; rreg HRn (8%bv) H8.
      all: pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS; pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 23; 26; 27]%bv HRn eq_refl) as GK7.
      all: clear HRn HR HK; fixregs.
      3: exact (ty_diag_c w c0 K fx A4 M4 model4 c R7 sel PS FZ CK X4 Htr BUD4 H2
               ltac:(rewrite (GK7 3%bv) by (clear; cbn; tauto); exact Y6gp) ltac:(rewrite (GK7 4%bv) by (clear; cbn; tauto); exact Y6tp) H8 C280').
      all: assert (OR7 : oregs w R7) by (eapply (oregs_glue w R6 R7 OR6 GS); [exact H2 | apply GK7; clear; cbn; tauto | apply GK7; clear; cbn; tauto | exact H8]).
      all: eapply (PUSHJ A4 M4 model4 R7 nwv X4 BUD4 OR7 LM4 IC4 FR4); [| | | exact Cnw];
        [rewrite (GK7 27%bv) by (clear; cbn; tauto); exact T27 | rewrite (GK7 23%bv) by (clear; cbn; tauto); exact T23 | rewrite (GK7 26%bv) by (clear; cbn; tauto); exact T26].
  Qed.
End PM.
