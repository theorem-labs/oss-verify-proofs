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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmZw PmODefsU1 PmStep4U1 PmArm_SpecU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
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

  Lemma ext_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> cellw SEGS M (w_sp w + 712) 4 wv ->
    srealizes SEGS (cfg fx R 0x68448 M model) K.
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
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
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
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10e05 37 37 _ B1 []);
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
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (wv) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS3) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M3 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R3cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R3cd (-4) _ _ B3 []);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | rewrite Zlength_nil; lia | exact DS3 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  #[local] Notation pm_span_push := (PmArm_SpecU1.pm_span_push CL).
  #[local] Notation EDESC_PTR := (cu_edesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition AREGS : list reg := [23; 24; 26; 27]%bv.
  Lemma seed_free_52 : seed_free [OT_VARIABLE_ID].
  Proof using. intros t [<- | []]. reflexivity. Qed.

  Theorem arm_EXTNUM_U1 : arm_stmt 7 0x67d74.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC. specialize (PK fx FZ FC). specialize (CK fx FZ FC).
    pose proof (AE_facts w I A M model c R 7 wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof MAXLEN as Hml. unfold V3MAX in V3B.
    destruct PO as (_ & C718 & _).
    destruct (ifr_ext w M FR) as (ext & Cext & Hext).
    assert (Q22' : getr R 22%bv = sxw wv) by (rewrite Q22; symmetry; apply sxw_sx32; lia).
    assert (Ht36 : 7 <> OT_RESULT_ID /\ 7 <> OT_LITERAL_INTEGER /\ 7 <> OT_LITERAL_STRING) by (unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING; lia).

    pm_seed R w c [Z_to_bv 64 ext; sxw wv].
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 40)] ++ OREGSEED)%list R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 32) 252) (N.to_nat 4) (EVar 39); KRange (EVar 39) 0 (2 ^ 31 - 1)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cext | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (22%bv) G22.
    pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK1.
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
    pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
    rewrite ?SymExec.alu64_add_lit in G12. rewrite ?w_add in G12 by lia. rewrite ?ext_val_sx4, ?sx32_small in G10 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 280) (w_sp w + 288)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 280) (w_sp w + 288)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    pose proof (x_ms X1) as MS1.
    eapply (pm_lookup_ext w A M1 model c fx R1 ext wv (w_sp w + 280) _ K X1 G10 ltac:(lia) ltac:(intros HH; discriminate HH)
              ltac:(intros _; split; [rewrite G11, TablStmts.sx32_prs; apply sxw_sx32; lia | split; [lia | exact G12]]) G2 ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)
              ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 M2 r d KEPT Hr Rr Fd Hfound Hhnd X2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G22 Q22b.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    assert (GK2 : forall r', In r' AREGS -> getr R2 r' = getr R r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
    clear KEPT G1 G2 G3 G4 G8 G10 G11 G12 G22 GK1 OR1.
    assert (AG02 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 280) (w_sp w + 288) a) M M2).
    { intros a Ha. rewrite (AG a ltac:(unfold w_sp0, PM_FRAME, zwin in *; lia)). apply (stores_in_agree _ _ _ _ ST1 ltac:(intros b Hb; exact Hb)). unfold zwin in *. lia. }
    assert (LM2 : loop_mem w M2) by (eapply (loop_mem_frame w M M2); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (IC2 : ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M2); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (FR2 : ifr w M2) by (eapply (ifr_agree w M M2); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (C718_2 : cellw SEGS M2 (w_sp w + 718) 2 1).
    { eapply (cellw_frame M M2); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    assert (C712_2 : cellw SEGS M2 (w_sp w + 712) 4 wv).
    { eapply (cellw_frame M M2); [exact C712 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    assert (Cext2 : cellw SEGS M2 (w_sp w + 252) 4 ext).
    { eapply (cellw_frame M M2); [exact Cext | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    pose proof (x_ms X2) as MS2. clear ST1 X1 MS1 AG AG02 MS X LM IC FR C718 C712 Cext.
    assert (OB2 : forall Rx, oregs w Rx -> OBASE w I A M2 model c Rx).
    { intros Rx ORx. split; [exact X2|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact ORx|]. split; [exact LM2|]. split; [exact IC2|]. split; [exact FR2|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R]. }
    assert (Hext32 : 0 <= ext < 2 ^ 32) by lia.

    assert (PB52 : forall Rx M3 (ret : Z),
              oregs w Rx -> (forall r', In r' AREGS -> getr Rx r' = getr R r') ->
              getr Rx 1%bv = Z_to_bv 64 ret -> (ret = 0x67dd4 \/ ret = 0x682c0) ->
              getr Rx 10%bv = Z_to_bv 64 (w_p w + 264) -> getr Rx 11%bv = Z_to_bv 64 (w_sp w + 304) ->
              stores_in (zwin (w_sp w + 304) (w_sp w + 308)) M2 M3 -> fld SEGS M3 (w_sp w + 304) 4 52 ->
              (forall A' R' M' model' (b' cap' : Z),
                  OBASE w I A' M' model' (set_v3 c (b', t3b (c_v3 c) ++ [OT_VARIABLE_ID], cap')) R' ->
                  (forall r', In r' AREGS -> getr R' r' = getr R r') ->
                  cellw SEGS M' (w_sp w + 718) 2 1 -> fld SEGS M' (w_sp w + 280) 8 d ->
                  srealizes SEGS (cfg fx R' ret M' model') K) ->
              srealizes SEGS (cfg fx Rx (vc_entry (ku_oty_pb ccU1)) M3 model) K).
    { intros Rx M3 ret ORx GKx Gra Hret Ga0 Ga1 ST3 F52 CONT.
      pose proof ORx as ORx'. destruct ORx' as (Xsp & Xgp & Xtp & Xs0 & _).
      assert (X3 : PMX w A M3 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M2 M3 model c (zwin (w_sp w + 304) (w_sp w + 308)));
          [exact X2 | exact ST3 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      eapply (pm_oty_pb w c0 K fx A M3 model c Rx (w_sp w + 304) 52 ret PS X3 Htr BUD).
      - split; [exact Gra|]. split; [destruct Hret as [-> | ->]; apply bv_eq; vm_compute; reflexivity|]. split; [lia|]. split; [exact Xsp|]. split; [exact Xgp | exact Xtp].
      - unfold O_V3. exact Ga0.
      - exact Ga1.
      - exact F52.
      - unfold OT_VARIABLE_ID. lia.
      - lia.
      - unfold w_sp0, PM_FRAME. lia.
      - apply mod16_4; [exact Gsp16 | reflexivity].
      - intros Heq. unfold vgrow. rewrite <- Heq. lia.
      - intros A5 R5 M5 model5 b' cap' X5 BUD5 KEPT5 AG5.
        assert (AG25 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 304) (w_sp w + 308) a) M2 M5).
        { intros a Ha. rewrite (AG5 a ltac:(unfold w_sp0, PM_FRAME; lia)). apply (stores_in_agree _ _ _ _ ST3 ltac:(intros b0 Hb0; exact Hb0)). unfold zwin in *. lia. }
        apply (CONT A5 R5 M5 model5 b' cap').
        + split; [exact X5|]. split; [exact Htr|]. split; [exact BUD5|]. split; [exact (oregs_kept w Rx R5 ORx KEPT5)|].
          split; [eapply (loop_mem_frame w M2 M5); [exact LM2 | lia | lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]|].
          split; [eapply (ictx_agree w M2 M5); [exact IC2 | lia | lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]|].
          split; [eapply (ifr_agree w M2 M5); [exact FR2 | lia | lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]|].
          cbn [set_v3 c_icount c_endian c_v3 t3b fst snd]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|].
          split; [exact MAC|]. apply Forall_app. split; [exact V3R|]. constructor; [unfold OT_VARIABLE_ID; lia | constructor].
        + intros r' Hr'. rewrite (KEPT5 r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GKx. exact Hr'.
        + eapply (cellw_frame M2 M5); [exact C718_2 | lia | cbn; lia | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]].
        + eapply fld_agree; [lia | cbn; lia | exact Fd | eapply agree_on_weaken; [exact AG25 | unfold zwin; cbn; intros; lia]]. }
    pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).

    pm_seed R2 w c [Z_to_bv 64 r; Z_to_bv 64 ext].
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] ++ OREGSEED)%list R2. seedHK HK w A M2 model c E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 252) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 (2 ^ 31 - 1); KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cext2 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X2) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    destruct (Z.eq_dec r 0) as [Hr0 | Hrn].
    -
      subst r. specialize (Hhnd eq_refl). cbn beta in Hhnd.
      pose proof (EDESC_PTR d ext wv Hhnd) as (Hd1 & Hd2 & Hd4).
      apply (know_more E M2 [KRange (EVar 39) 0 0]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }

      assert (TAIL : forall A' M' model' c' R' (pre : list Z),
                OBASE w I A' M' model' c' R' -> (forall r', In r' AREGS -> getr R' r' = getr R r') ->
                cellw SEGS M' (w_sp w + 718) 2 1 -> fld SEGS M' (w_sp w + 280) 8 d ->
                c_widx c' = c_widx c -> c_v1 c' = c_v1 c -> c_v2 c' = c_v2 c -> PmLoopU1.nodes c' = PmLoopU1.nodes c ->
                t3b (c_v3 c') = t3b (c_v3 c) ++ pre -> seed_free pre -> Zlen pre <= 1 ->
                c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c -> ~ In OT_RESULT_ID pre ->
                srealizes SEGS (cfg fx R' 0x682c0 M' model') K).
      { intros A' M' model' c' R' pre OB' GK' C718' Fd' Ewidx Ev1 Ev2 Enodes Epre SFpre Hpre Em1c Em2c Em3c NRpre.
        pose proof OB' as OB''. destruct OB'' as (X' & Htr' & BUD' & OR' & LM' & IC' & FR' & _). pose proof (x_ms X') as MS'.
        pose proof OR' as OR''. destruct OR'' as (Ysp & Ygp & Ytp & Ys0 & Ys1 & Ys2 & Ys3 & Ys4 & Ys5 & Ys9).
        pose (E' := Eseed R' (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                              Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c') :: Z_to_bv 64 (c_widx c') :: [Z_to_bv 64 d])).
        seedHR HR' E' ([(2%bv, EVar 32); (8%bv, EVar 33)] ++ OREGSEED)%list R'. seedHK HK' w A' M' model' c' E' X'.
        apply (know_more E' M' [KWord (SA (EVar 32) 280) (N.to_nat 8) (EVar 39); KRange (EVar 39) 0x10000 (2 ^ 40); KAlign (EVar 39) 4]) in HK'.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [eapply fld_cellw; [exact Fd' | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply krange_var; [evs; reflexivity | lia | lia].
             - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
        xruns HR' HK' 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R8.
        rreg HRn (1%bv) G1. rreg HRn (10%bv) G10.
        pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK8.
        assert (OR8 : oregs w R8) by (oregs_seeded HRn Ygp Ytp).
        pose proof OR8 as OR''. destruct OR'' as (G2 & G3 & G4 & G8 & _). clear HRn HR' HK'.
        eapply (pm_edesc_operands w A' M' model' c' fx R8 _ K X' (ex_intro _ d (ex_intro _ ext (ex_intro _ wv (conj Hhnd G10)))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
        intros R9 KEPT POST. destruct (POST d ext wv Hhnd G10) as (p & l & Hg & RS & Hp4 & Qa0' & Qa1').
        keptQ KEPT G2 Qsp9. keptQ KEPT G8 Qs09. keptQ KEPT G3 Qgp9. keptQ KEPT G4 Qtp9.
        pose proof (oregs_kept w R8 R9 OR8 KEPT) as OR9.
        assert (GK9 : forall r', In r' AREGS -> getr R9 r' = getr R r').
        { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). rewrite (GK8 r' Hr'). apply GK'. exact Hr'. }
        clear KEPT POST GK8 OR8 G1 G2 G3 G4 G8 G10.
        pose proof (go_len_ext G GOK ext wv l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.
        pose proof OR9 as OR''. destruct OR'' as (_ & _ & _ & _ & Zs1 & Zs2 & Zs3 & Zs4 & Zs5 & Zs9).

        try clear E'. pose (E' := Eseed R9 (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                                        Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c') :: Z_to_bv 64 (c_widx c') :: [Z_to_bv 64 p; Z_to_bv 64 (Zlen l)])).
        seedHR HR' E' ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (11%bv, EVar 40)] ++ OREGSEED)%list R9. seedHK HK' w A' M' model' c' E' X'.
        xruns HR' HK' 100%nat (0x67f4c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R10.
        rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
        pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK10.
        assert (OR10 : oregs w R10) by (oregs_seeded HRn Qgp9 Qtp9). clear HRn HR' HK'.
        assert (OB10 : OBASE w I A' M' model' c' R10).
        { split; [exact X'|]. split; [exact Htr'|]. split; [exact BUD'|]. split; [exact OR10|]. split; [exact LM'|]. split; [exact IC'|]. split; [exact FR'|].
          destruct OB' as (_ & _ & _ & _ & _ & _ & _ & REST). exact REST. }
        eapply (pm_span_push w c0 K fx I A' M' model' c' R10 p l PS OB10 G10 G11 RS Hp4 (go_ext_zw G GOK ext wv l Hg)).
        + apply Forall_forall. intros x Hx. eapply (go_range G GOK l x); [right; right; exists ext, wv; exact Hg | exact Hx].
        + exact Hll.
        + rewrite Epre, Zlen_app. unfold V3MAX in *. lia.
        + intros A'' M'' model'' R'' b'' cap'' l' El' SF' Hlen' Hr' OB'' GK'' AG''.
          eapply (PK A'' M'' model'' _ R'' 1 (pre ++ l') OB'').
          * rewrite (GK'' 27%bv), (GK10 27%bv), (GK9 27%bv) by (clear; inl). exact Q27.
          * rewrite (GK'' 23%bv), (GK10 23%bv), (GK9 23%bv) by (clear; inl). exact Q23.
          * rewrite (GK'' 26%bv), (GK10 26%bv), (GK9 26%bv) by (clear; inl). exact Q26.
          * eapply (cellw_frame M' M''); [exact C718' | lia | cbn; lia | eapply agree_on_weaken; [exact AG'' | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
          * left. lia.
          * cbn [set_v3 c_widx]. exact Ewidx. * cbn [set_v3 c_v1]. exact Ev1. * cbn [set_v3 c_v2]. exact Ev2.
          * unfold PmLoopU1.nodes in *. cbn [set_v3 c_m1 c_m2 c_m3]. lia.
          * cbn [set_v3 c_v3 t3b fst snd]. rewrite El', Epre, <- app_assoc. reflexivity.
          * apply seed_free_app; [exact SFpre | exact SF'].
          * rewrite Zlen_app. lia.
          * right. exact Ht36.
          * cbn [set_v3 c_m2]. exact Em2c.
          * left. cbn [set_v3 c_m1]. exact Em1c.
          * left. cbn [set_v3 c_m3]. exact Em3c.
          * intros Hin3. apply in_app_or in Hin3. destruct Hin3 as [Hin3|Hin3]; [exact (NRpre Hin3) | exact (notrid_ext CL _ _ _ _ _ Hg El' Hin3)]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10.
      pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK3.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2).
      pose proof OR3 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      rewrite ?ext_val_sx4, ?sx32_small in G10 by lia.
      eapply (pm_is_nonsemantic w A M2 model c fx R3 _ K X2 (ex_intro _ ext (conj Hext32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 KEPT (b & Hb).
      keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4.
      pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
      assert (GK4 : forall r', In r' AREGS -> getr R4 r' = getr R r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). rewrite (GK3 r' Hr'). apply GK2. exact Hr'. }
      clear KEPT G1 G2 G3 G4 G8 G10 GK3 OR3.
      pose proof OR4 as OR'. destruct OR' as (_ & _ & _ & _ & Fs1 & Fs2 & Fs3 & Fs4 & Fs5 & Fs9).

      pm_seed R4 w c [Z_to_bv 64 (if b then 1 else 0)].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] ++ OREGSEED)%list R4. seedHK HK w A M2 model c E X2.
      apply (know_more E M2 [KRange (EVar 39) (if b then 1 else 0) (if b then 1 else 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | destruct b; lia | destruct b; lia]. }
      destruct b.
      +
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
        pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK5.
        assert (OR5 : oregs w R5) by (oregs_seeded HRn Qgp4 Qtp4). clear HRn HR HK.
        rewrite ?SymExec.alu64_add_lit in G10. rewrite ?SymExec.alu64_add_lit in G11. rewrite ?w_add in G11 by lia.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
        apply (PB52 R5 M3 0x682c0 OR5 ltac:(intros r' Hr'; rewrite (GK5 r' Hr'); apply GK4; exact Hr') G1 ltac:(right; reflexivity) G10 G11 ltac:(unfold M3; stin) ltac:(unfold M3; rdback)).
        intros A5 R6 M5 model5 b' cap' OB5 GK6 C718_5 Fd5.
        apply (TAIL A5 M5 model5 _ R6 [OT_VARIABLE_ID] OB5 GK6 C718_5 Fd5); try reflexivity.
        all: first [exact seed_free_52 | rewrite Zlen_cons, Zlen_nil; lia | exact notrid_varid].
      +
        xruns HR HK 100%nat (0x682c0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK5.
        assert (OR5 : oregs w R5) by (oregs_seeded HRn Qgp4 Qtp4). clear HRn HR HK.
        apply (TAIL A M2 model c R5 [] (OB2 R5 OR5) ltac:(intros r' Hr'; rewrite (GK5 r' Hr'); apply GK4; exact Hr') C718_2 Fd); try reflexivity.
        all: first [rewrite app_nil_r; reflexivity | exact PmZw.seed_free_nil | rewrite Zlen_nil; lia | intros []].
    -
      apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10.
      pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK3.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2).
      pose proof OR3 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      rewrite ?ext_val_sx4, ?sx32_small in G10 by lia.
      eapply (pm_is_nonsemantic w A M2 model c fx R3 _ K X2 (ex_intro _ ext (conj Hext32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 KEPT (b & Hb).
      keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4.
      pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
      assert (GK4 : forall r', In r' AREGS -> getr R4 r' = getr R r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). rewrite (GK3 r' Hr'). apply GK2. exact Hr'. }
      clear KEPT G1 G2 G3 G4 G8 G10 GK3 OR3.
      pose proof OR4 as OR'. destruct OR' as (_ & _ & _ & _ & Fs1 & Fs2 & Fs3 & Fs4 & Fs5 & Fs9).

      pm_seed R4 w c [Z_to_bv 64 (if b then 1 else 0)].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] ++ OREGSEED)%list R4. seedHK HK w A M2 model c E X2.
      apply (know_more E M2 [KRange (EVar 39) (if b then 1 else 0) (if b then 1 else 0); KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | destruct b; lia | destruct b; lia].
           - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X2) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      destruct b.
      +
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
        pose proof (syms_id_sound _ _ _ _ AREGS HRn eq_refl) as GK5.
        assert (OR5 : oregs w R5) by (oregs_seeded HRn Qgp4 Qtp4). clear HRn HR HK.
        rewrite ?SymExec.alu64_add_lit in G10. rewrite ?SymExec.alu64_add_lit in G11. rewrite ?w_add in G11 by lia.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
        apply (PB52 R5 M3 0x67dd4 OR5 ltac:(intros r' Hr'; rewrite (GK5 r' Hr'); apply GK4; exact Hr') G1 ltac:(left; reflexivity) G10 G11 ltac:(unfold M3; stin) ltac:(unfold M3; rdback)).
        clear G1 G10 G11. intros A5 R6 M5 model5 b' cap' OB5 GK6 C718_5 Fd5.
        pose proof OB5 as OB5'. destruct OB5' as (X5 & _ & _ & OR6 & _). pose proof (x_ms X5) as MS5.
        pose proof OR6 as OR6'. destruct OR6' as (Ysp & Ygp & Ytp & Ys0 & _).

        try clear E. pose (E := Eseed R6 (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                                     Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c) :: Z_to_bv 64 (c_widx c) :: (@nil word))).
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6.
        assert (HK : know_ok SEGS E M5 pm_kn).
        { apply (pmx_know w A5 M5 model5 (set_v3 c (b', t3b (c_v3 c) ++ [OT_VARIABLE_ID], cap')) E X5); evs; reflexivity. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R7.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
        pose proof (syms_id_sound _ _ _ _ (PmODefsU1.OSREGS ++ AREGS) HRn eq_refl) as GK7.
        clear HRn HR HK. fixregs.
        assert (OR7 : oregs w R7).
        { eapply (PmInstU1.loop_regs_glue w R6 R7); [exact OR6 | intros r0 Hr0; apply GK7; apply in_app_iff; left; exact Hr0 | exact G2 | exact G3 | exact G4 | exact G8]. }
        eapply (PK A5 M5 model5 _ R7 1 [OT_VARIABLE_ID]).
        * destruct OB5 as (_ & Htr5 & BUD5 & _ & REST). split; [exact X5|]. split; [exact Htr5|]. split; [exact BUD5|]. split; [exact OR7 | exact REST].
        * rewrite (GK7 27%bv), (GK6 27%bv) by (clear; inl). exact Q27.
        * rewrite (GK7 23%bv), (GK6 23%bv) by (clear; inl). exact Q23.
        * rewrite (GK7 26%bv), (GK6 26%bv) by (clear; inl). exact Q26.
        * exact C718_5.
        * left. lia.
        * reflexivity. * reflexivity. * reflexivity.
        * unfold PmLoopU1.nodes. cbn [set_v3 c_m1 c_m2 c_m3]. lia.
        * cbn [set_v3 c_v3 t3b fst snd]. reflexivity.
        * exact seed_free_52.
        * rewrite Zlen_cons, Zlen_nil. lia.
        * right. exact Ht36.
        * reflexivity. * left; reflexivity. * left; reflexivity. * exact notrid_varid.
      +
        xruns HR HK 100%nat (0x68448 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
        clear HRn HR HK. fixregs. rewrite Qgp4 in G3. rewrite Qtp4 in G4.
        exact (ext_diag w c0 K fx A M2 model c R5 wv PS FZ CK X2 Htr BUD G2 G3 G4 G8 C712_2).
  Qed.
End PM.
