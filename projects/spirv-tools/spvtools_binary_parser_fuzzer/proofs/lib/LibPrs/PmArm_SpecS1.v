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
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1 HWord.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmZw PmODefsS1 PmStep4S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
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
  #[local] Notation pm_spec_lookup := (PmStep4S1.pm_spec_lookup CL).
  Definition pm_operand_type_str := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_operand_type_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma sxw_big : forall v, 2 ^ 31 <= v < 2 ^ 32 -> sxw v = Z_to_bv 64 (v + 2 ^ 64 - 2 ^ 32).
  Proof using.
    intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [lia|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- (Z.mod_add (v - 2 ^ 32) 1 (2 ^ 64)) by lia. f_equal. lia.
  Qed.

  Lemma pm_span_push : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (p : Z) (l : list Z),
    PMS w c0 K -> OBASE w I A M model c R ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (Zlen l) ->
    ro_span SEGS Ly.L p l -> p mod 4 = 0 -> seed_free l -> Forall (fun x => 0 <= x < 2 ^ 31) l -> Zlen l <= g_maxlen G ->
    Zlen (t3b (c_v3 c)) + g_maxlen G <= V3MAX ->
    (forall A' M' model' R' (b' cap' : Z) (l' : list Z),
        push_types l (t3b (c_v3 c)) = t3b (c_v3 c) ++ l' -> seed_free l' -> Zlen l' <= Zlen l -> Forall (fun x => 0 <= x < 2 ^ 31) l' ->
        OBASE w I A' M' model' (set_v3 c (b', push_types l (t3b (c_v3 c)), cap')) R' ->
        (forall r, In r [18; 21; 22; 23; 25; 26; 27]%bv -> getr R' r = getr R r) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w /\ ~ zwin (w_sp w + 272) (w_sp w + 288) a) M M' ->
        srealizes SEGS (cfg fx R' 0x670c4 M' model') K) ->
    srealizes SEGS (cfg fx R 0x670b0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R p l PS OB Qa0 Qa1 RS Hp4 SFl Hrange Hll Hmax CONT.
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof RS as RS'. destruct RS' as (Rp0 & Rp1 & _). assert (Hl0 : 0 <= Zlen l) by (unfold Zlen; lia). pose proof MAXLEN as Hml.
    pm_seed R w c [Z_to_bv 64 p; Z_to_bv 64 (Zlen l)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (11%bv, EVar 40)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [18; 21; 22; 23; 25; 26; 27]%bv HRn eq_refl) as GK3.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R3 OR GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
    rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G10 by lia.
    replace (Z_to_bv 5 (Z.of_N 20)) with (20%bv : reg) in G11 by (apply bv_eq; reflexivity). rewrite Qs4 in G11.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
    assert (ST2 : stores_in (zwin (w_sp w + 272) (w_sp w + 288)) M M2) by (unfold M2; stin).
    assert (X2 : PMX w A M2 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M2 model c (zwin (w_sp w + 272) (w_sp w + 288)));
        [exact X | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (Fp : fld SEGS M2 (w_sp w + 272) 8 p) by (unfold M2; rdback).
    assert (Fl : fld SEGS M2 (w_sp w + 272 + 8) 8 (Zlen l)) by (unfold M2; replace (w_sp w + 272 + 8) with (w_sp w + 280) by lia; rdback).
    pose proof (x_ms X2) as MS2.
    eapply (pm_push_types w c0 K fx A M2 model c R3 (w_sp w + 272) p _ l PS X2 Htr BUD ltac:(cregs_tac G1 G2 G3 G4) G10);
      [unfold O_V3; exact G11 | exact Fp | exact Fl | exact RS | exact Hp4 | lia | exact Hrange
      | lia | unfold w_sp0, PM_FRAME; lia | lia |].
    intros A3 R4 M3 model3 b' cap' X3 BUD3 KEPT AG.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
    assert (GK4 : forall r, In r [18; 21; 22; 23; 25; 26; 27]%bv -> getr R4 r = getr R r).
    { intros r Hr. rewrite (KEPT r) by (revert Hr; clear; intros Hr; apply in_reg_list; cbn in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity). apply GK3. exact Hr. }
    destruct (push_types_facts l (t3b (c_v3 c)) SFl Hrange) as (l' & El' & Hlen' & SF' & Hr').
    assert (AG' : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 272) (w_sp w + 288) a) M M3).
    { intros a Ha. rewrite (AG a ltac:(unfold w_sp0, PM_FRAME; lia)). apply (stores_in_agree _ _ _ _ ST2 ltac:(intros b Hb; exact Hb)). unfold zwin in *. lia. }
    apply (CONT A3 M3 model3 R4 b' cap' l' El' SF' Hlen' Hr').
    - split; [exact X3|]. split; [exact Htr|]. split; [exact BUD3|]. split; [exact OR4|].
      split; [eapply (PmBody1S1.loop_mem_frame w M M3); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG' | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (PmBody1S1.ictx_agree w M M3); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG' | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (ifr_agree w M M3); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG' | unfold zwin; cbn; intros; lia]]|].
      cbn [set_v3 c_icount c_endian c_v3 t3b fst snd]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|].
      split; [exact MAC|]. rewrite El'. apply Forall_app. split; [exact V3R | exact Hr'].
    - exact GK4.
    - exact AG'.
  Qed.

  Lemma spec_diagA : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 18%bv = sxw wv -> 0 <= wv < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x67444 M model) K.
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
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10556 8 8 _ B1 []);
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
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (18%bv) G18.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    assert (Hlit3 : 0 <= 8 < 2 ^ 32) by lia.
    eapply (pm_operand_type_str w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ 8 (conj Hlit3 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (18%bv) G18. rreg HRn (21%bv) G21.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rename G21 into Q21p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18. keptQ KEPT Q21p Q21p_. clear Q21p. rename Q21p_ into Q21p.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (21%bv, EVar 40)] R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x13e3f 2 2 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X5 BUD5 DS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_u32 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (wv) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X6 BUD6 DS6. pose proof (x_ms X7) as MS7.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS7) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M7 (w_sp w + 272 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R7cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R7cd (-4) _ _ B7 []);
      [exact PS | exact X7 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD7 | rewrite Zlength_nil; lia | exact DS7 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  Lemma spec_diagB : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x67874 M model) K.
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
    eapply (pm_pdiagE w c0 K fx A M model c R1 (-1) _ []);
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
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-1) _ 0x13e42 39 39 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M2 (w_sp w + 272 + 360) ((-1) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-1) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw ((-1) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R2cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R2cd (-1) _ _ B2 []);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-1) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-1) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-1) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) [sxw ((-1) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) Re ((-1) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T26 ltac:(lia)).
  Qed.

  Lemma in_skipn : forall {T} n (l : list T) x, In x (skipn n l) -> In x l.
  Proof using. intros T n l x Hx. rewrite <- (firstn_skipn n l). apply in_app_iff. right. exact Hx. Qed.

  Lemma ro_span_skip2 : forall p l, ro_span SEGS Ly.L p l -> 2 <= Zlen l -> ro_span SEGS Ly.L (p + 8) (skipn 2 l).
  Proof using.
    intros p l (R1 & R2 & R3) Hl.
    assert (EL : Zlen (skipn 2 l) = Zlen l - 2) by (unfold Zlen in *; rewrite length_skipn; lia).
    split; [lia|]. split; [lia|]. intros M RC i Hi.
    destruct (R3 M RC (i + 2) ltac:(lia)) as [Hr Hf].
    assert (EN : Znth (i + 2) l = Znth i (skipn 2 l)).
    { unfold Znth. rewrite nth_skipn. f_equal. lia. }
    rewrite <- EN. split; [exact Hr|]. replace (p + 8 + 4 * i) with (p + 4 * (i + 2)) by lia. exact Hf.
  Qed.

  Theorem arm_SPECOP_S1 : arm_stmt 8 0x67430.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R wv PS FZ IP HAE PK CK AACC. specialize (PK fx FZ). specialize (CK fx FZ).
    pose proof (cl_spec_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as SPEC3.
    pose proof (AE_facts w I A M model c R 8 wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q18 & Q21 & Q22 & Q23 & Q25 & PO & C680).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof MAXLEN as Hml.
    destruct PO as (_ & C686 & _).
    assert (Q18' : getr R 18%bv = sxw wv) by (rewrite Q18; symmetry; apply sxw_sx32; lia).
    assert (Ht36 : 8 <> OT_RESULT_ID /\ 8 <> OT_LITERAL_INTEGER /\ 8 <> OT_LITERAL_STRING) by (unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING; lia).
    destruct (Z.lt_ge_cases wv (2 ^ 31)) as [Hsmall | Hbig].
    2: {
         assert (Q18b : getr R 18%bv = Z_to_bv 64 (wv + 2 ^ 64 - 2 ^ 32)) by (rewrite Q18'; apply sxw_big; lia).
         pm_seed R w c [Z_to_bv 64 (wv + 2 ^ 64 - 2 ^ 32)].
         seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39)] R. seedHK HK w A M model c E X.
         apply (know_more E M [KRange (EVar 39) (2 ^ 63) (2 ^ 64 - 1)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (0x67444 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
         postrun. name_run HRn R1.
         rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (18%bv) G18.
         clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite <- Q18b, Q18' in G18.
         exact (spec_diagA w c0 K fx A M model c R1 wv PS FZ CK X Htr BUD G2 G3 G4 G8 G18 Hword). }

    assert (Q18s : getr R 18%bv = Z_to_bv 64 wv) by (rewrite Q18'; apply sxw_small'; lia).
    pm_seed R w c [Z_to_bv 64 wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KRange (EVar 39) 0 (2 ^ 31 - 1)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK1. rreg HRn (18%bv) G18.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_spec_lookup w A M model c fx R1 wv 0x67440 K X G10 G11 ltac:(lia) G2 G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 M2 r KEPT Hr Rr Hspec X2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G18 Q18b.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    assert (GK2 : forall r', In r' [21; 23; 25]%bv -> getr R2 r' = getr R r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
    clear KEPT G1 G2 G3 G4 G8 G10 G11 G18 GK1 OR1.
    assert (AG02 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880) M M2) by (intros a Ha; apply AG; unfold w_sp0, PM_FRAME; lia).
    assert (LM2 : loop_mem w M2) by (eapply (PmBody1S1.loop_mem_frame w M M2); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (IC2 : ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M M2); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (FR2 : ifr w M2) by (eapply (ifr_agree w M M2); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
    assert (C686_2 : cellw SEGS M2 (w_sp w + 686) 2 1).
    { eapply (PmBody1S1.cellw_frame M M2); [exact C686 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    pose proof (x_ms X2) as MS2. clear AG AG02 MS X LM IC FR C686 C680.

    pm_seed R2 w c [Z_to_bv 64 r; Z_to_bv 64 wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (18%bv, EVar 40)] R2. seedHK HK w A M2 model c E X2.
    destruct (Z.eq_dec r 0) as [Hr0 | Hrn].
    2: { apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (0x67444 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
         postrun. name_run HRn R3.
         rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (18%bv) G18.
         clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite <- Q18s, Q18' in G18.
         exact (spec_diagA w c0 K fx A M2 model c R3 wv PS FZ CK X2 Htr BUD G2 G3 G4 G8 G18 Hword). }
    subst r. pose proof (proj1 Hspec eq_refl) as HSP.
    apply (know_more E M2 [KRange (EVar 39) 0 0; KRange (EVar 40) 0 (2 ^ 31 - 1)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil; eapply krange_var; [evs; reflexivity | lia | lia | evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK3. rreg HRn (18%bv) G18.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
    rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite w_add in G11 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
    assert (ST3 : stores_in (zwin (w_sp w + 752) (w_sp w + 760)) M2 M3) by (unfold M3; stin).
    assert (X3 : PMX w A M3 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M2 M3 model c (zwin (w_sp w + 752) (w_sp w + 760)));
        [exact X2 | exact ST3 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    pose proof (x_ms X3) as MS3.
    eapply (pm_lookup_opcode w A M3 model c fx R3 wv 0 (w_sp w + 752) _ K X3 G10 ltac:(lia) ltac:(intros _; exact G11) ltac:(intros HH; discriminate HH)
              G2 ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia) ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Hr Rr Hspec. intros R4 M4 r d KEPT Hr Rr Fd Hfound Hhnd X4 AG.
    keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4. keptQ KEPT G18 Q18d.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
    assert (GK4 : forall r', In r' [21; 23; 25]%bv -> getr R4 r' = getr R2 r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK3. exact Hr'. }
    clear KEPT G1 G2 G3 G4 G8 G10 G11 G18 GK3 OR3.
    assert (AG24 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 752) (w_sp w + 760) a) M2 M4).
    { intros a Ha. rewrite (AG a ltac:(unfold w_sp0, PM_FRAME, zwin in *; lia)). apply (stores_in_agree _ _ _ _ ST3 ltac:(intros b Hb; exact Hb)). unfold zwin in *. lia. }
    assert (OB4 : forall Rx, oregs w Rx -> OBASE w I A M4 model c Rx).
    { intros Rx ORx. split; [exact X4|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact ORx|].
      split; [eapply (PmBody1S1.loop_mem_frame w M2 M4); [exact LM2 | lia | lia | eapply agree_on_weaken; [exact AG24 | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (PmBody1S1.ictx_agree w M2 M4); [exact IC2 | lia | lia | eapply agree_on_weaken; [exact AG24 | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (ifr_agree w M2 M4); [exact FR2 | lia | lia | eapply agree_on_weaken; [exact AG24 | unfold zwin; cbn; intros; lia]]|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R]. }
    assert (C686_4 : cellw SEGS M4 (w_sp w + 686) 2 1).
    { eapply (PmBody1S1.cellw_frame M2 M4); [exact C686_2 | lia | cbn; lia | eapply agree_on_weaken; [exact AG24 | unfold zwin; cbn; intros; lia]]. }
    pose proof (x_ms X4) as MS4. clear ST3 X3 MS3 AG.

    pm_seed R4 w c [Z_to_bv 64 r; Z_to_bv 64 (d mod 2 ^ 64)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R4. seedHK HK w A M4 model c E X4.
    destruct (Z.eq_dec r 0) as [Hr0' | Hrn'].
    2: { apply (know_more E M4 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (0x67874 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
         postrun. name_run HRn R5.
         rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
         clear HRn HR HK. fixregs. rewrite Qgp4 in G3. rewrite Qtp4 in G4.
         exact (spec_diagB w c0 K fx A M4 model c R5 PS FZ CK X4 Htr BUD G2 G3 G4 G8). }
    subst r. specialize (Hhnd eq_refl). cbn beta in Hhnd.
    apply (know_more E M4 [KRange (EVar 39) 0 0; KWord (SA (EVar 32) 752) (N.to_nat 8) (EVar 40)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_var; [eapply fld_cellw; [unfold CRep.fld in *; rewrite <- (LibMaskBits.Z_to_bv_mod64 d); exact Fd | cbn; pose proof (Z.mod_pos_bound d (2 ^ 64)); lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK5.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
    rewrite <- (LibMaskBits.Z_to_bv_mod64 d) in G10.
    eapply (pm_idesc_operands w A M4 model c fx R5 _ K X4 (ex_intro _ d (ex_intro _ wv (conj Hhnd G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R6 KEPT POST. destruct (POST d wv Hhnd G10) as (p & l & Hg & RS & Hp4 & Qa0' & Qa1').
    keptQ KEPT G2 Qsp6. keptQ KEPT G8 Qs06. keptQ KEPT G3 Qgp6. keptQ KEPT G4 Qtp6.
    pose proof (oregs_kept w R5 R6 OR5 KEPT) as OR6.
    assert (GK6 : forall r', In r' [21; 23; 25]%bv -> getr R6 r' = getr R4 r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK5. exact Hr'. }
    clear KEPT POST GK5 OR5 G1 G2 G3 G4 G8 G10.
    pose proof (SPEC3 wv l HSP Hg) as Hl3.
    pose proof (go_len_op G GOK wv l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.
    pose proof RS as RS'. destruct RS' as (Rp0 & Rp1 & _).

    pm_seed R6 w c [Z_to_bv 64 p; Z_to_bv 64 (Zlen l)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (11%bv, EVar 40)] R6. seedHK HK w A M4 model c E X4.
    apply (know_more E M4 [KRange (EVar 39) (2 ^ 16) (2 ^ 47); KRange (EVar 40) 3 1024]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil; eapply krange_var; [evs; reflexivity | lia | lia | evs; reflexivity | lia | pose proof (go_maxlen G GOK); lia]. }
    xruns HR HK 100%nat (0x670b0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK7.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R6 R7 OR6 GS G2 G3 G4 G8 (or_introl G9)) as OR7. clear GS G9.
    rewrite SymExec.alu64_add_lit in G10, G11.
    assert (EL2 : Zlen (skipn 2 l) = Zlen l - 2) by (unfold Zlen in *; rewrite length_skipn; lia).
    eapply (pm_span_push w c0 K fx I A M4 model c R7 (p + 8) (skipn 2 l) PS (OB4 R7 OR7) G10).
    - rewrite EL2. replace (Zlen l - 2) with (Zlen l + -2) by lia. exact G11.
    - apply ro_span_skip2; [exact RS | lia].
    - rewrite <- Zplus_mod_idemp_l, Hp4. reflexivity.
    - exact (go_spec_zw G GOK wv l HSP Hg).
    - apply Forall_forall. intros x Hx. eapply (go_range G GOK l x); [left; exists wv; exact Hg | exact (in_skipn 2 l x Hx)].
    - lia.
    - lia.
    - intros A' M' model' R' b' cap' l' El' SF' Hlen' Hr' OB' GK' AG'.
      eapply (PK A' M' model' _ R' 1 l' OB').
      + rewrite (GK' 21%bv), (GK7 21%bv), (GK6 21%bv), (GK4 21%bv), (GK2 21%bv) by (clear; inl). exact Q21.
      + rewrite (GK' 23%bv), (GK7 23%bv), (GK6 23%bv), (GK4 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
      + rewrite (GK' 25%bv), (GK7 25%bv), (GK6 25%bv), (GK4 25%bv), (GK2 25%bv) by (clear; inl). exact Q25.
      + eapply (PmBody1S1.cellw_frame M4 M'); [exact C686_4 | lia | cbn; lia | eapply agree_on_weaken; [exact AG' | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      + left. lia.
      + reflexivity. + reflexivity. + reflexivity.
      + unfold PmLoopS1.nodes. cbn [set_v3 c_m1 c_m2 c_m3]. lia.
      + cbn [set_v3 c_v3 t3b fst snd]. exact El'.
      + exact SF'.
      + lia.
      + right. exact Ht36.
      + reflexivity. + left; reflexivity. + left; reflexivity.
      + exact (notrid_spec CL _ _ _ _ HSP Hg El').
  Qed.
End PM.
