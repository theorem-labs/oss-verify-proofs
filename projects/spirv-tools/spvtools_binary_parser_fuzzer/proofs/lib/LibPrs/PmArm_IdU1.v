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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmZw PmODefsU1 PmStep4U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
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

  Lemma id_diag0 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x68184 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
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
    assert (Cerr : cell4 SEGS M2 (w_sp w + 304 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R2cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R2cd (-10) _ _ B2 []);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma id_diag1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> cellw SEGS M (w_sp w + 712) 4 wv ->
    srealizes SEGS (cfg fx R 0x68378 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R wv PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C712.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C712) as Hwv. cbn in Hwv.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
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
    eapply (cellw_frame _ M2) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C712. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-10) _ (wv) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
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
    assert (Cerr : cell4 SEGS M4 (w_sp w + 304 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R4cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R4cd (-10) _ _ B4 []);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | rewrite Zlength_nil; lia | exact DS4 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Theorem arm_ID_U1 : forall t, (t = 1 \/ t = 42) -> arm_stmt t 0x67bc4.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht12 w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC. specialize (PK fx FZ FC). specialize (CK fx FZ FC).
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (ipure_ranges I IP) as (Riwc & Rop).
    destruct PO as (_ & C718 & _).
    assert (Q22' : getr R 22%bv = sxw wv) by (rewrite Q22; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q22z : getr R 22%bv = Z_to_bv 64 0) by (rewrite Q22', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, ELit 0)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x68184 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      exact (id_diag0 w c0 K fx A M model c R1 PS FZ CK X Htr BUD G2 G3 G4 G8).
    -
      pm_seed R w c [sxw wv; Z_to_bv 64 (i_op I); Z_to_bv 64 (i_io I); Z_to_bv 64 t; Z_to_bv 64 (c_widx c - i_io I)].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (26%bv, EVar 40); (23%bv, EVar 41); (27%bv, EVar 42); (24%bv, EVar 43)] ++ OREGSEED)%list R.
      seedHK HK w A M model c E X.
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_eq_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22. rreg HRn (26%bv) G26. rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (24%bv) G24.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
      pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 720) (w_sp w + 724)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 720) (w_sp w + 724)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 720) (w_sp w + 724) a) M M1).
      { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
      assert (LM1 : loop_mem w M1) by (eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (C718' : cellw SEGS M1 (w_sp w + 718) 2 1).
      { eapply (cellw_frame M M1); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      assert (C712' : cellw SEGS M1 (w_sp w + 712) 4 wv).
      { eapply (cellw_frame M M1); [exact C712 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.

      assert (PUSH1 : forall Rx, oregs w Rx -> getr Rx 27%bv = Z_to_bv 64 t -> getr Rx 23%bv = Z_to_bv 64 (i_io I) -> getr Rx 26%bv = Z_to_bv 64 (i_op I) ->
                      srealizes SEGS (cfg fx Rx 0x67f60 M1 model) K).
      { intros Rx ORx X27 X23 X26. eapply (PK A M1 model c Rx 1 []).
        - split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact ORx|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
          split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
        - exact X27. - exact X23. - exact X26. - exact C718'. - left; lia.
        - reflexivity. - reflexivity. - reflexivity.
        - change (Z.min 1 1) with 1. lia.
        - rewrite app_nil_r. reflexivity. - exact PmZw.seed_free_nil. - rewrite PmZw.Zlen_nil. lia. - left; reflexivity.
        - reflexivity. - left; reflexivity. - left; reflexivity. - intros []. }
      assert (Rop32 : 0 <= i_op I < 2 ^ 32) by lia.
      eapply (pm_is_ext_inst w A M1 model c fx R1 _ K X1 (ex_intro _ (i_op I) (conj Rop32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 KEPT (b & Hb).
      keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2.
      keptQ KEPT G22 Q22b. keptQ KEPT G26 Q26b. keptQ KEPT G23 Q23b. keptQ KEPT G27 Q27b. keptQ KEPT G24 Q24b.
      pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
      pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).
      clear KEPT G1 G2 G3 G4 G8 G10 G22 G26 G23 G27 G24 OR1.

      pm_seed R2 w c [Z_to_bv 64 (c_widx c - i_io I); Z_to_bv 64 (if b then 1 else 0); Z_to_bv 64 (i_io I); Z_to_bv 64 t; Z_to_bv 64 (i_op I); sxw wv].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (24%bv, EVar 39); (10%bv, EVar 40); (23%bv, EVar 41); (27%bv, EVar 42); (26%bv, EVar 43); (22%bv, EVar 44)] ++ OREGSEED)%list R2.
      seedHK HK w A M1 model c E X1.
      apply (know_more E M1 [KRange (EVar 40) (if b then 1 else 0) (if b then 1 else 0); KRange (EVar 39) 0 65535]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | destruct b; lia | destruct b; lia].
           - eapply krange_var; [evs; reflexivity | lia | lia]. }
      destruct b.
      2: {
           xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
           postrun. name_run HRn R3.
           rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (26%bv) G26.
           assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2). clear HRn HR HK.
           apply (PUSH1 R3 OR3 G27 G23 G26). }
      destruct (Z.eq_dec (c_widx c - i_io I) 3) as [Ho3 | Hon3].
      2: { xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
           { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?br_ne, ?br_eq by lia; bool_lia. }
           postrun. name_run HRn R3.
           rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (26%bv) G26.
           assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2). clear HRn HR HK.
           apply (PUSH1 R3 OR3 G27 G23 G26). }

      pose proof (loop_mem_cell w M1 48 (w_p w + 176) LM1 ltac:((first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ])) ltac:(lia)) as C48.
      apply (know_more E M1 [KWord (SA (EVar 32) 48) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 176))]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [exact C48 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?br_ne, ?br_eq by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
      rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (26%bv) G26.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2).
      pose proof OR3 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      rewrite ?SymExec.alu64_add_lit in G10. rewrite ?w_add in G10 by lia. rewrite ?w_add in G11 by lia.
      eapply (pm_find_m3 w A M1 model c fx R3 (w_sp w + 712) wv 0x67bf4 K X1 ltac:(unfold O_M3; exact G10) G11 C712' ltac:(lia) ltac:(lia) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 p KEPT Hp Hfound.
      keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4. keptQ KEPT G23 Q23d. keptQ KEPT G27 Q27d. keptQ KEPT G26 Q26d.
      pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
      clear KEPT G1 G2 G3 G4 G8 G10 G11 G23 G27 G26 OR3.
      destruct Hfound as [-> | (Hp0 & Hp47 & Hpal & v & Hin & Cv)].
      +
        pm_seed R4 w c (@nil word).
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R4. seedHK HK w A M1 model c E X1.
        xruns HR HK 100%nat (0x68378 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
        clear HRn HR HK. fixregs. rewrite Qgp4 in G3. rewrite Qtp4 in G4.
        exact (id_diag1 w c0 K fx A M1 model c R5 wv PS FZ CK X1 Htr BUD G2 G3 G4 G8 C712').
      +
        pose proof (proj1 Cv) as Hv. cbn in Hv.
        pose proof (PmLoopU1.m3ok_val _ _ _ _ (proj1 (proj2 (proj2 (proj2 MAC)))) Hin) as Hv31.
        pose proof OR4 as OR'. destruct OR' as (_ & _ & _ & _ & Fs1 & Fs2 & Fs3 & Fs4 & Fs5 & Fs9).
        pm_seed R4 w c [Z_to_bv 64 p; Z_to_bv 64 v; Z_to_bv 64 (i_io I); Z_to_bv 64 t; Z_to_bv 64 (i_op I)].
        seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (23%bv, EVar 41); (27%bv, EVar 42); (26%bv, EVar 43)] ++ OREGSEED)%list R4. seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KWord (SA (EVar 39) 20) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 (2 ^ 31 - 1); KRange (EVar 39) 1 (2 ^ 47); KAlign (EVar 39) 8]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [exact Cv | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply krange_var; [evs; reflexivity | lia | lia].
             - eapply krange_var; [evs; reflexivity | lia | lia].
             - eapply kalign_var; [evs; reflexivity | lia | lia | pose proof (Z.div_mod p 16 ltac:(lia)); rewrite Hpal in *; replace p with ((2 * (p / 16)) * 8) by lia; apply Z_mod_mult]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (26%bv) G26.
        assert (OR5 : oregs w R5) by (oregs_seeded HRn Qgp4 Qtp4). clear HRn HR HK.
        rewrite ?ext_val_sx4, ?sx32_small by lia.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
        assert (ST2 : stores_in (zwin (w_sp w + 252) (w_sp w + 256)) M1 M2) by (unfold M2; stin).
        assert (X2 : PMX w A M2 model c).
        { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 M2 model c (zwin (w_sp w + 252) (w_sp w + 256)));
            [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
        assert (AG2 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 252) (w_sp w + 256) a) M1 M2).
        { eapply stores_in_agree; [exact ST2 | intros b' Hb'; unfold zwin in *; lia]. }
        assert (FR2 : ifr w M2) by (unfold M2; apply ifr_store4; [exact FR1 | left; split; [reflexivity | lia] | lia | lia | lia]).
        eapply (PK A M2 model c R5 1 []).
        * split; [exact X2|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR5|].
          split; [eapply (loop_mem_frame w M1 M2); [exact LM1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]|].
          split; [eapply (ictx_agree w M1 M2); [exact IC1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]|].
          split; [exact FR2|]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
        * exact G27. * exact G23. * exact G26.
        * eapply (cellw_frame M1 M2); [exact C718' | lia | cbn; lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]].
        * left; lia.
        * reflexivity. * reflexivity. * reflexivity.
        * change (Z.min 1 1) with 1. lia.
        * rewrite app_nil_r. reflexivity. * exact PmZw.seed_free_nil. * rewrite PmZw.Zlen_nil. lia. * left; reflexivity.
        * reflexivity. * left; reflexivity. * left; reflexivity. * intros [].
  Qed.
End PM.
