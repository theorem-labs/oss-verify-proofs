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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmZw PmStep4S1 PmStep5S1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
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
  #[local] Notation pm_v3_pb := (PmStep4S1.pm_v3_pb CL).
  #[local] Notation pm_oty_pb := (PmStep4S1.pm_oty_pb CL).
  #[local] Notation pm_find_m1 := (PmStep4S1.pm_find_m1 CL).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).
  #[local] Notation pm_spec_lookup := (PmStep4S1.pm_spec_lookup CL).
  #[local] Notation pm_h5 := (PmStep5S1.pm_h5 CL).

  Ltac fixregs2 := fixregs;
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity).
  Lemma ext_val_zx2 : forall v, 0 <= v < 2 ^ 16 -> ext_val false 0 2 (Z_to_bv 64 v) = Z_to_bv 64 v.
  Proof using. intros v Hv. apply ext_val_zx_id. rewrite u64_of_Z by lia. cbn. lia. Qed.

  #[local] Notation pmx_updS := (pmx_upd SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation live_splitS := (live_split SEGS Ly.L MI ST).
  #[local] Notation live_joinS := (live_join SEGS Ly.L MI ST).
  #[local] Notation hi_unownedS := (hi_unowned MI ly_img_low ly_rw_img).
  #[local] Notation HCL := (cl_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pmx_roomS := (pmx_room SEGS Ly.L MI ST (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (cl_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)).
  #[local] Notation pmx_room2S := (pmx_room2 SEGS Ly.L MI ST (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (cl_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)).

  Definition set_m1 (c : pmc) (m : Z * Z * list (Z * (Z * Z))) : pmc :=
    {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
       c_m1 := m; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.
  Definition set_m3 (c : pmc) (m : Z * Z * list (Z * (Z * Z))) : pmc :=
    {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
       c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := m; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.

  Lemma umapx_set_val24 : forall (A : AS MI) M obj bl bc l1 l2 (p k v v' : Z),
    umapx MI 24 (nval24 SEGS) A M obj bl bc (l1 ++ (p, (k, v)) :: l2) -> 0 <= v' < 2 ^ 32 ->
    umapx MI 24 (nval24 SEGS) A (wbytes M (Z_to_bv 64 (p + 20)) (word_to_le_bytes 4 (Z_to_bv 64 v'))) obj bl bc (l1 ++ (p, (k, v')) :: l2).
  Proof using AC MI.
    intros A M obj bl bc l1 l2 p k v v' U Hv'.
    set (M' := wbytes M (Z_to_bv 64 (p + 20)) (word_to_le_bytes 4 (Z_to_bv 64 v'))).
    destruct U as [UH Ual Ulo Uhi Ubseq Uload Ublive Ublal Ubllo Ublhi Ublobj Ubkt Unodup Uchain Unode Unapart].
    assert (Hinp : In (p, (k, v)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    destruct (Unode p k v Hinp) as (Hlive & Hp0 & Hp47 & Hpal & Ck8 & Ck16 & Rk & Nv & Apo & Apb).
    assert (Efst : map fst (l1 ++ (p, (k, v')) :: l2) = map fst (l1 ++ (p, (k, v)) :: l2)) by (rewrite !map_app; reflexivity).
    assert (Elen : HRep.Zlength (l1 ++ (p, (k, v')) :: l2) = HRep.Zlength (l1 ++ (p, (k, v)) :: l2)) by (unfold HRep.Zlength; rewrite !length_app; reflexivity).
    assert (Ehd : forall l, hdaddr ((p, (k, v')) :: l) = hdaddr ((p, (k, v)) :: l)) by (intros; reflexivity).
    assert (Ehd2 : hdaddr (l1 ++ (p, (k, v')) :: l2) = hdaddr (l1 ++ (p, (k, v)) :: l2)) by (destruct l1; reflexivity).

    assert (AG : forall a n, 0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> apart (p + 20) 4 a n -> HRepFacts.agree_on M M' a n).
    { intros a n Ha Han Hap. unfold M'. apply agree_on_wbytes_out; rewrite ?length_N_to_le_bytes; rewrite ?u64_of_Z; try lia. exact Hap. }
    assert (KEEP : forall a (wd : N) x, cellw SEGS M a wd x -> 0 <= a -> a + Z.of_N wd <= 2 ^ 47 -> apart (p + 20) 4 a (Z.of_N wd) -> cellw SEGS M' a wd x).
    { intros a wd x C Ha Hw Hap. eapply cellw_agree; [exact C | apply AG; [lia | lia | exact Hap] | lia | lia]. }

    assert (OTHER : forall q kq vq, In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2) -> q <> p -> apart q 24 p 24).
    { intros q kq vq Hq Hne. apply Unapart; [| | exact Hne]; apply in_map_iff; [exists (q, (kq, vq)) | exists (p, (k, v))]; auto. }
    constructor; rewrite ?Efst, ?Elen; try assumption.
    -   destruct UH as [H1 H2 H3 H4 H5 H6]. constructor; rewrite ?Ehd2, ?Elen; unfold cell8, cell4 in *;
        try (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
      unfold M'. apply defined_wbytes. exact H6.
    -   intros i Hi. destruct (Ubkt i Hi) as (b & Cb & Hb). exists b. split.
      + unfold cell8 in *. apply KEEP; [exact Cb | lia | cbn; lia |].
        assert (Hbc : bc <> 0) by lia. pose proof (Apb Hbc) as Ap. unfold apart in *. cbn. lia.
      + unfold bucket_ok in *. rewrite Efst. destruct Hb as [Hb|[Hb|(Hb1 & Hb2 & Hb3)]]; [left; exact Hb | right; left; exact Hb | right; right].
        split; [exact Hb1|]. split; [destruct l1; discriminate|]. rewrite Hb3. destruct l1; reflexivity.
    -
      assert (CH : forall (ents : list (Z * (Z * Z))), chain SEGS M ents ->
                     (forall q kq vq, In (q, (kq, vq)) ents -> q = p \/ apart q 24 p 24) ->
                     (forall q kq vq, In (q, (kq, vq)) ents -> 0 < q /\ q + 24 <= 2 ^ 47) ->
                     chain SEGS M' ents).
      { intros ents. induction ents as [|[q [kq vq]] ents IH]; intros C Hq Hr; [exact Logic.I|]. cbn [chain] in C |- *. destruct C as [C1 C2].
        split; [| apply IH; [exact C2 | intros q' k' u' H'; apply (Hq q' k' u'); right; exact H' | intros q' k' u' H'; apply (Hr q' k' u'); right; exact H']].
        unfold cell8 in *. destruct (Hr q kq vq (or_introl eq_refl)) as [Hq0 Hq47].
        apply KEEP; [exact C1 | lia | cbn; lia |]. destruct (Hq q kq vq (or_introl eq_refl)) as [-> | Hap]; unfold apart in *; cbn; lia. }
      assert (CH2 : chain SEGS M' (l1 ++ (p, (k, v)) :: l2)).
      { apply CH; [exact Uchain | |].
        - intros q kq vq Hq. destruct (Z.eq_dec q p) as [-> | Hne]; [left; reflexivity | right; exact (OTHER q kq vq Hq Hne)].
        - intros q kq vq Hq. destruct (Unode q kq vq Hq) as (_ & H0 & H47 & _). lia. }
      clear - CH2 Ehd. revert CH2. generalize l2. induction l1 as [|[q [kq vq]] l1 IH]; intros l2' C; cbn [chain app] in C |- *.
      + exact C.
      + destruct C as [C1 C2]. split; [| apply IH; exact C2]. destruct l1; [cbn in C1 |- *; exact C1 | exact C1].
    -   intros q kq vq Hq.
      assert (NP : ~ In p (map fst l1) /\ ~ In p (map fst l2)).
      { rewrite map_app in Unodup. cbn [map fst] in Unodup. apply (proj1 (list_relations.list.NoDup_app _ _)) in Unodup. destruct Unodup as (N1 & NX & N2).
        split.
        - intros H1. refine (NX p _ _); [apply list_elem_of_In; exact H1 | apply list_elem_of_In; left; reflexivity].
        - intros H2. apply (proj1 (list_relations.list.NoDup_cons _ _)) in N2. destruct N2 as [N2 _]. apply N2. apply list_elem_of_In. exact H2. }
      destruct NP as [NP1 NP2].
      apply in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]].
      + assert (Hne : q <> p) by (intros ->; apply NP1; apply in_map_iff; exists (p, (kq, vq)); auto).
        assert (Hq' : In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; left; exact Hq).
        destruct (Unode q kq vq Hq') as (L1 & L2 & L3 & L4 & C8 & C16 & RK & NV & AP1 & AP2). pose proof (OTHER q kq vq Hq' Hne) as AP.
        unfold cell8, cell4, nval24 in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
      + injection Hq. intros -> -> ->.
        unfold cell8, cell4, nval24 in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          try (apply KEEP; [assumption | lia | cbn; lia | unfold apart; cbn; lia]).
        unfold M'. change 4%nat with (N.to_nat 4). apply cellw_store; cbn; lia.
      + assert (Hne : q <> p) by (intros ->; apply NP2; apply in_map_iff; exists (p, (kq, vq)); auto).
        assert (Hq' : In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; right; right; exact Hq).
        destruct (Unode q kq vq Hq') as (L1 & L2 & L3 & L4 & C8 & C16 & RK & NV & AP1 & AP2). pose proof (OTHER q kq vq Hq' Hne) as AP.
        unfold cell8, cell4, nval24 in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
  Qed.

  Lemma pmx_upd_blk : forall (i : cix) (w : pmw MI ST) A M M' model c c' (W : Z -> Prop) (b : Z * Z),
    PMX w A M model c -> stores_in W M M' -> In b (cblocks i c) ->
    (forall a, W a -> fst b <= a < fst b + snd b) ->
    (forall j, j <> i -> csame j c c') ->
    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c -> c_tr c' = c_tr c ->
    cblocks i c' = cblocks i c ->
    crep SEGS Ly.L MI ST w i A M' c' ->
    PMX w A M' model c'.
  Proof using AC MI ST.
    intros i w A M M' model c c' W b X SI Hb HW HS Ew Ei Ee Ef Et Eb REP.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct b as [q k].
    assert (Hl : In (q, k) (live MI A)).
    { apply (cblk_live w (q, k) X). apply (proj2 (in_cblk c (q, k))). exists i. exact Hb. }
    destruct (ai_live_block MI A M model q k AI Hl) as (Hk0 & Hq16 & Hq0 & Hqc & Hpay). cbn [fst snd] in HW.
    assert (AI' : ainv MI A M' model).
    { eapply stores_in_ainv; [exact AI | exact SI |]. intros a Ha. exact (proj1 (Hpay a (HW a Ha))). }
    eapply (pmx_updS w i A M model c A M' model c' 0 W X AI' (x_ms X) eq_refl eq_refl);
      [ | unfold PM_FRAME; lia | intros a Ha; left; right; exists (q, k); split; [exact Hb | exact (HW a Ha)]
      | intros a Ha Hz; exfalso; pose proof (HW a Ha); unfold zwin, w_sp0, PM_FRAME in *; lia
      | exact HS | exact Ew | exact Ei | exact Ee | exact Ef | exact Et | exact REP |].
    - apply eff_store; [| exact (proj2 SI)]. intros a Hf _. apply (proj1 SI). exact Hf.
    - eapply (live_joinS w A c c' i HS Et). rewrite Eb. exact (live_splitS w A M model c i X).
  Qed.

  Lemma pm_m1_setval : forall (w : pmw MI ST) A M model c l1 l2 (p k v v' : Z),
    PMX w A M model c -> t3c (c_m1 c) = l1 ++ (p, (k, v)) :: l2 -> 0 <= v' < 2 ^ 32 ->
    PMX w A (wbytes M (Z_to_bv 64 (p + 20)) (word_to_le_bytes 4 (Z_to_bv 64 v'))) model
        (set_m1 c (t3a (c_m1 c), t3b (c_m1 c), l1 ++ (p, (k, v')) :: l2)).
  Proof using AC MI ST.
    intros w A M model c l1 l2 p k v v' X E Hv'.
    pose proof (x_m1 X) as U. rewrite E in U.
    pose proof U as U0. destruct U0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ Unode _].
    destruct (Unode p k v ltac:(apply in_app_iff; right; left; reflexivity)) as (Hlive & Hp0 & Hp47 & _).
    assert (SI : stores_in (zwin (p + 20) (p + 24)) M (wbytes M (Z_to_bv 64 (p + 20)) (word_to_le_bytes 4 (Z_to_bv 64 v')))) by stin.
    eapply (pmx_upd_blk CM1 w A M _ model c _ _ (p, 24) X SI).
    - cbn [cblocks]. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity|]. rewrite E. apply in_app_iff. right. left. reflexivity.
    - intros a Ha. unfold zwin in Ha. cbn. lia.
    - intros j Hj. destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)].
    - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - cbn [cblocks set_m1 c_m1 t3a t3b t3c fst snd]. rewrite E. unfold umap_blocks. rewrite !map_app. reflexivity.
    - cbn [crep set_m1 c_m1 t3a t3b t3c fst snd]. exact (umapx_set_val24 A M _ _ _ l1 l2 p k v v' U Hv').
  Qed.

  Lemma pm_emplace_m1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (key keyp tupp ret : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> PmLoopS1.macct c ->
    2 * (Zlen (t3c (c_m1 c)) + 1) <= w_n w + 2 ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_p w + O_M1) -> getr R 11%bv = Z_to_bv 64 keyp -> getr R 13%bv = Z_to_bv 64 tupp ->
    cell4 SEGS M keyp key -> cellw SEGS M tupp 8 keyp ->
    w_sp w <= keyp -> keyp + 4 <= w_sp0 w - 104 -> w_sp w <= tupp -> tupp + 8 <= w_sp0 w - 104 ->
    (forall (fx' : FPState) A' R' M' model' (p v : Z) (m1' : Z * Z * list (Z * (Z * Z))),
        frm_zero (@fp_csr fx') -> PMX w A' M' model' (set_m1 c m1') -> pm_bud (w_n w) (set_m1 c m1') -> PmLoopS1.macct (set_m1 c m1') ->
        Zlen (t3c (c_m1 c)) <= Zlen (t3c m1') <= Zlen (t3c (c_m1 c)) + 1 ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> In (p, (key, v)) (t3c m1') -> 0 <= v < 2 ^ 32 ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (hc_emplace_u32 HConstsS1.hc) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R key keyp tupp ret PS FZ X Htr BUD MACC ACC1 CR Ha0 Ha1 Ha3 Ckey Ctup Hk1 Hk2 Ht1 Ht2 CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (S1 & S2 & S3 & S4). pose proof (x_caps X) as (_ & _ & HNMAX).
    pose proof (cl_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof BUD as BUD'. destruct BUD' as ((Bn1 & Bn2 & Bn3) & B1 & B2 & B3 & _).
    destruct (c_m1 c) as [[bl bc] ents] eqn:Em1.
    pose proof (x_m1 X) as U. rewrite Em1 in U. cbn [t3a t3b t3c fst snd] in U. unfold O_M1 in U |- *.
    unfold PmLoopS1.macct in MACC. rewrite ?Em1 in *. cbn [t3a t3b t3c fst snd] in ACC1, MACC, B1, Bn1.
    destruct MACC as (MACC1 & MACC2 & MACC3 & M3OK).
    pose proof U as U0. destruct U0 as [_ _ _ _ Ubseq Uload _ _ _ _ _ _ _ _ _ _].
    unfold Zlen, Zlength in *.
    assert (Hz123 : 0 <= Z.of_nat (length ents) /\ 0 <= Z.of_nat (length (t3c (c_m2 c))) /\ 0 <= Z.of_nat (length (t3c (c_m3 c)))) by lia.
    assert (Hlast : bc <> BSEQ_LAST) by (unfold BSEQ_LAST; lia).
    assert (WD : forall t n, w_sp w + 880 - w_STK w <= t -> t + n <= w_sp w + 880 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (t + i - (w_sp w + 880 - w_STK w))) with (t + i) in D by lia. exact D. }
    assert (HES : EMPLACE_STACK (NEW_STACK SEGS Ly.L MI) (MALLOC_STACK MI) <= 8304 /\ 96 <= EMPLACE_STACK (NEW_STACK SEGS Ly.L MI) (MALLOC_STACK MI)).
    { unfold EMPLACE_STACK, NEW_STACK. lia. }
    destruct HES as [HES1 HES2].
    pose proof (proj1 Ctup) as Rkeyp. cbn in Rkeyp.
    eapply ((cl_emplace_u32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (w_s w) R M model (w_sp w) ret (w_p w + 96) bl bc keyp tupp keyp key ents K).
    - eapply pmx_cregs_callB; [exact X | exact CR | unfold PM_FRAME; lia].
    - exact FZ.
    - exact Ha0. - exact Ha1. - exact Ha3.
    - exact U.
    - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unownedS; [exact AI | lia].
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold w_sp0, PM_FRAME; lia].
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold w_sp0, PM_FRAME; lia].
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold w_sp0, PM_FRAME; lia].
    - exact Ckey. - exact Ctup. - exact Ckey.
    - exact (x_roc X).
    - unfold Zlen, Zlength in *. lia.
    - unfold LIB_NMAX in *. lia.
    - exact Hlast.
    - eapply pmx_roomS; [exact X | exact BUD | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | lia].
    - intros Hfull. pose proof (PmStep5S1.bseq_next_le bc Ubseq Hlast) as [Hb1 H28].
      eapply pmx_room2S; [exact X | exact BUD | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | lia | lia | lia].
    - intros fx' A' R' M' model' p v bl' bc' ents' inserted rehashed RB FZ' Hp Hinsr U' Hin Hnoins Hins Hnorh Hrh LA EF.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      set (c' := set_m1 c (bl', bc', ents')).
      pose proof U' as U1. destruct U1 as [_ _ _ _ Ubseq' Uload' Ublive' _ Ubl0' _ _ _ _ _ Unode' _]. unfold Zlen, Zlength in Uload', Hrh |- *.
      assert (X' : PMX w A' M' model' c').
      { eapply (pmx_updS w CM1 A M model c A' M' model' c' (EMPLACE_STACK (NEW_STACK SEGS Ly.L MI) (MALLOC_STACK MI)) _ X AI' MS' FS' FDS' EF);
          [unfold PM_FRAME; lia | | | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; unfold O_M1; exact U' |].
        + intros a [Ha|Ha].
          * left. destruct (umap_foot_cases 24 (w_p w + 96) bl bc ents a Ha) as [H|H];
              [left; unfold zwin, O_M1; cbn [chdr fst snd]; unfold O_M1; lia | right; cbn [cblocks]; rewrite Em1; cbn [t3a t3b t3c fst snd]; exact H].
          * right; left. destruct (umap_foot_cases 24 (w_p w + 96) bl' bc' ents' a Ha) as [H|H];
              [left; unfold zwin, O_M1; cbn [chdr fst snd]; unfold O_M1; lia | right; cbn [cblocks c' set_m1 c_m1 t3a t3b t3c fst snd]; exact H].
        + intros a [Ha|Ha] Hz; unfold zwin, w_sp0, PM_FRAME in Hz; exfalso.
          * destruct (umap_foot_cases 24 (w_p w + 96) bl bc ents a Ha) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
            destruct (ai_live_block MI A M model q k AI (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U Hb)) as (_ & _ & _ & Hc' & _). lia.
          * destruct (umap_foot_cases 24 (w_p w + 96) bl' bc' ents' a Ha) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
            destruct (ai_live_block MI A' M' model' q k AI' (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U' Hb)) as (_ & _ & _ & Hc' & _). lia.
        + eapply (live_joinS w A' c c' CM1); [intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)] | reflexivity |].
          cbn [cblocks c' set_m1 c_m1 t3a t3b t3c fst snd].
          pose proof (live_splitS w A M model c CM1 X) as P0. cbn [cblocks] in P0. rewrite Em1 in P0. cbn [t3a t3b t3c fst snd] in P0.
          destruct (PmStep5S1.lapply_app_inv _ _ _ _ LA) as (lv1 & LA1 & LA2).
          unfold umap_blocks in P0 |- *. rewrite <- app_assoc in P0 |- *.
          destruct (PmStep5S1.umap_xfer_ins 24 (live MI A) lv1 (if bc =? 0 then [] else [(bl, 8 * bc)]) _ p (key, 0) ents ents' inserted
                      (ai_live_nodup MI A M model AI) P0
                      ltac:(intros Hf; destruct (Hnoins Hf) as [-> _]; reflexivity)
                      ltac:(intros Ht; exact (proj2 (Hins Ht))) LA1) as [P1 N1].
          assert (Hrh' : rehashed = true -> bc' <> 0) by (intros Hr; destruct (Hrh Hr) as [_ ->]; pose proof (PmStep5S1.bseq_next_le bc Ubseq Hlast); lia).
          exact (PmStep5S1.umap_xfer_rh lv1 (live MI A') _ bl bc bl' bc' rehashed N1 (ai_live_nodup MI A' M' model' AI') ltac:(lia) P1 Hnorh Hrh' LA2). }
      assert (LEN : Z.of_nat (length ents') <= Z.of_nat (length ents) + 1 /\ Z.of_nat (length ents) <= Z.of_nat (length ents')).
      { destruct inserted.
        - pose proof (Permutation_length (proj2 (Hins eq_refl))) as E. rewrite E. cbn [length]. lia.
        - destruct (Hnoins eq_refl) as [-> _]. lia. }
      assert (BC' : 8 * bc' <= 16 * Z.of_nat (length ents') + 504).
      { destruct rehashed.
        - destruct (Hrh eq_refl) as [Hfull ->]. pose proof (PmStep5S1.bseq_next_le bc Ubseq Hlast). lia.
        - destruct (Hnorh eq_refl) as [-> ->]. lia. }
      destruct (Unode' p key v Hin) as (_ & _ & _ & _ & _ & _ & _ & NV & _). pose proof (proj1 NV) as Rv. cbn in Rv.
      eapply (CONT fx' A' R' M' model' p v (bl', bc', ents') FZ' X'); [| | cbn [t3c snd]; unfold Zlen, Zlength in *; lia | exact KEPT | exact Hp | exact Hin | exact Rv |].
      + unfold pm_bud. cbn [c' set_m1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd]. unfold Zlen, Zlength in *. rewrite Htr.
        destruct BUD as ((C1a & C1b & C1c) & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). rewrite Em1 in *. cbn [t3a t3b t3c fst snd] in *.
        pose proof (PmStep5S1.bseq_next_le bc Ubseq Hlast) as [_ H28].
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); try assumption; try lia.
        all: cbn [length Z.of_nat]; try lia; try (intros b0 Hb0; exfalso; exact Hb0).
      + unfold PmLoopS1.macct. cbn [c' set_m1 c_m1 c_m2 c_m3 t3a t3b t3c fst snd]. unfold Zlen, Zlength in *. split; [lia|]. split; [lia|]. split; [lia | exact M3OK].
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | lia |].
        intros a Ha. split; [unfold w_sp0, PM_FRAME; exact Ha|]. unfold w_sp0, PM_FRAME in Ha. intros [Hf|Hf].
        * destruct (umap_foot_cases 24 (w_p w + 96) bl bc ents a Hf) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
          destruct (ai_live_block MI A M model q k AI (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U Hb)) as (_ & _ & _ & Hc' & _). lia.
        * destruct (umap_foot_cases 24 (w_p w + 96) bl' bc' ents' a Hf) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
          destruct (ai_live_block MI A' M' model' q k AI' (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U' Hb)) as (_ & _ & _ & Hc' & _). lia.
  Qed.

  Lemma rid_diag_a : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x67838 M model) K.
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
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x14224 21 21 _ B1 []);
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

  Lemma rid_diag_b : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> forall wv : Z, cellw SEGS M (w_sp w + 244) 4 wv ->
    srealizes SEGS (cfg fx R 0x675d0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 wv C244. pose proof (proj1 C244) as Rword. cbn in Rword.
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
    eapply (cellw_frame _ M1) in C244; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x126e9 3 3 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros Ab Rbc Mb modelb Bb Xb BUDb KEPT _ DSb AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ Mb) in C244; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms Xb) as MSb.

    pm_seed Rbc w (set_tr c (Bb ++ [])) [Z_to_bv 64 wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] Rbc. seedHK HK w Ab Mb modelb (set_tr c (Bb ++ [])) E Xb.
    apply (know_more E Mb [KWord (SA (EVar 32) 244) (N.to_nat 4) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil. eapply kword_var; [exact C244 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Rb2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia. rewrite ext_val_sx4 in G11 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx Ab Mb modelb (set_tr c (Bb ++ [])) Rb2 (-10) _ wv _ Bb []);
      [exact PS | exact Xb | reflexivity | exact BUDb | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DSb | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros Ac Rcc Mc modelc Bc Xc BUDc KEPT _ DSc AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11.
    try clear Xb BUDb DSb. pose proof (x_ms Xc) as MSc.

    pm_seed Rcc w (set_tr c (Bc ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] Rcc. seedHK HK w Ac Mc modelc (set_tr c (Bc ++ [])) E Xc.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Rc2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx Ac Mc modelc (set_tr c (Bc ++ [])) Rc2 (-10) _ 0x1340d 26 26 _ Bc []);
      [exact PS | exact Xc | reflexivity | exact BUDc | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DSc | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear Xc BUDc DSc. pose proof (x_ms X2) as MS2.
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

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  Definition pm_generates_type := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_generates_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma w2le4_sxw : forall v, word_to_le_bytes 4 (sxw v) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v. unfold sxw. change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N. apply word_to_le_bytes_swrap. cbn; lia. Qed.

  Lemma relro_kimg : forall (w : pmw MI ST) A M model c E (lo hi : Z),
    PMX w A M model c -> 0xe6000 <= lo -> hi <= 0xee000 -> kentry_ok SEGS E M (KImg lo hi).
  Proof using AC MI ST.
    intros w A M model c E lo hi X Hlo Hhi. apply kimg_abs; [lia | lia |]. intros i Hi.
    pose proof (pmx_img_ro_clear w X (Z_to_bv 64 i)) as IR. rewrite u64_of_Z in IR by lia.
    apply IR; cbn [ly_img ly_rw Ly.L]; rewrite in_ranges_1; lia.
  Qed.

  Theorem arm_RESULTID_S1 : arm_stmt 3 0x675b8.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R wv PS FZ IP HAE PK CK AACC.
    pose proof (AE_facts w I A M model c R 3 wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q18 & Q21 & Q22 & Q23 & Q25 & PO & C680).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof (ipure_ranges I IP) as (Riwc & Rop).
    destruct PO as (_ & C686 & _).
    assert (Q18' : getr R 18%bv = sxw wv) by (rewrite Q18; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q18z : getr R 18%bv = Z_to_bv 64 0) by (rewrite Q18', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, ELit 0)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x67838 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      exact (rid_diag_a w c0 K fx A M model c R1 PS FZ (CK fx FZ) X Htr BUD G2 G3 G4 G8).
    -
      pm_seed R w c [sxw wv].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39)] R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 80) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 96))]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w M 80); [exact LM | (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_eq_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK1. rreg HRn (18%bv) G18.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G10, G11 by lia. rewrite w2le4_sxw.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 244) (w_sp w + 248)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 244) (w_sp w + 248)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 244) (w_sp w + 248) a) M M1).
      { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
      assert (LM1 : loop_mem w M1) by (eapply (PmBody1S1.loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (FR1 : ifr w M1) by (unfold M1; apply ifr_store4; [exact FR | right; right; reflexivity | lia | lia | lia]).
      assert (C686' : cellw SEGS M1 (w_sp w + 686) 2 1).
      { eapply (PmBody1S1.cellw_frame M M1); [exact C686 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      assert (C244 : cellw SEGS M1 (w_sp w + 244) 4 wv) by (split; [cbn; lia | unfold M1; rdback]).
      pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.
      eapply (pm_find_m1 w A M1 model c fx R1 (w_sp w + 244) wv 0x675cc K X1 ltac:(unfold O_M1; exact G10) G11 C244 ltac:(lia) ltac:(lia) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 p KEPT Hp Hfound.
      keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2.
      pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
      assert (GK2 : forall r', In r' [21; 23; 25]%bv -> getr R2 r' = getr R r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply PmStepS1.in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
      assert (Q21b : getr R2 21%bv = Z_to_bv 64 3) by (rewrite (GK2 21%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]); exact Q21).
      assert (Q23b : getr R2 23%bv = Z_to_bv 64 (i_io I)) by (rewrite (GK2 23%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]); exact Q23).
      assert (Q25b : getr R2 25%bv = Z_to_bv 64 (i_op I)) by (rewrite (GK2 25%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]); exact Q25).
      clear KEPT G1 G2 G3 G4 G8 G10 G11 GK1 OR1.
      destruct Hfound as [-> | (Hp0 & Hp47 & Hpal & v0 & Hin0 & Cv0)].
      2: {
           pm_seed R2 w c [Z_to_bv 64 p].
           seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M1 model c E X1.
           apply (know_more E M1 [KRange (EVar 39) 1 (2 ^ 47)]) in HK.
           2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
           xruns HR HK 100%nat (0x675d0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
           postrun. name_run HRn R3.
           rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
           clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4.
           exact (rid_diag_b w c0 K fx A M1 model c R3 PS FZ (CK fx FZ) X1 Htr BUD G2 G3 G4 G8 wv C244). }

      pm_seed R2 w c [Z_to_bv 64 (i_op I)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0); (25%bv, EVar 39)] R2. seedHK HK w A M1 model c E X1.
      apply (know_more E M1 [KRange (EVar 39) 0 65535]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (25%bv) G25.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [18; 21; 23]%bv HRn eq_refl) as GK3.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      rewrite ?ext_val_zx2 in G10 by lia.
      assert (Rop32 : 0 <= i_op I < 2 ^ 32) by lia.
      eapply (pm_generates_type w A M1 model c fx R3 _ K X1 (ex_intro _ (i_op I) (conj Rop32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 KEPT (b & Gb & _). pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4. keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04.
      assert (GK4 : forall r', In r' [18; 21; 23; 25]%bv -> getr R4 r' = getr R2 r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply PmStepS1.in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity).
        revert Hr'. clear - GK3 Q25b G25. intros Hr'. cbn in Hr'. decompose [or] Hr'; try contradiction; subst r'; first [apply GK3; (first [solve [clear; cbn; tauto] | cbn; tauto]) | rewrite G25, Q25b; reflexivity]. }
      clear G1 G2 G3 G4 G8 G10 KEPT OR3.
      pose proof FR1 as FR1'. destruct FR1' as (ext & tid & rid & _ & _ & _ & Ctid & _ & _ & _ & _). pose proof (proj1 Ctid) as Rtid. cbn in Rtid.
      set (M2 := wbytes M1 (Z_to_bv 64 (w_sp w + 272)) (word_to_le_bytes 8 (Z_to_bv 64 (w_sp w + 244)))).
      assert (ST2 : stores_in (zwin (w_sp w + 272) (w_sp w + 280)) M1 M2) by (unfold M2; stin).
      assert (X2 : PMX w A M2 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 M2 model c (zwin (w_sp w + 272) (w_sp w + 280)));
          [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG2 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880 /\ ~ zwin (w_sp w + 272) (w_sp w + 280) a) M1 M2).
      { eapply stores_in_agree; [exact ST2 | intros b' Hb'; unfold zwin in *; lia]. }
      assert (LM2 : loop_mem w M2) by (eapply (PmBody1S1.loop_mem_frame w M1 M2); [exact LM1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]).
      assert (IC2 : ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (PmBody1S1.ictx_agree w M1 M2); [exact IC1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]).
      assert (FR2 : ifr w M2) by (eapply (ifr_agree w M1 M2); [exact FR1 | lia | lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]).
      assert (C686_2 : cellw SEGS M2 (w_sp w + 686) 2 1).
      { eapply (PmBody1S1.cellw_frame M1 M2); [exact C686' | lia | cbn; lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]. }
      assert (C244_2 : cellw SEGS M2 (w_sp w + 244) 4 wv).
      { eapply (PmBody1S1.cellw_frame M1 M2); [exact C244 | lia | cbn; lia | eapply agree_on_weaken; [exact AG2 | unfold zwin; cbn; intros; lia]]. }
      assert (Ctup : cellw SEGS M2 (w_sp w + 272) 8 (w_sp w + 244)) by (split; [cbn; lia | unfold M2; rdback]).

      assert (TAILE : forall Rx (vs : Z), oregs w Rx -> getr Rx 18%bv = Z_to_bv 64 (PrsGrammar.sx32 vs) -> 0 <= vs < 2 ^ 32 ->
                getr Rx 10%bv = Z_to_bv 64 (w_p w + O_M1) -> getr Rx 11%bv = Z_to_bv 64 (w_sp w + 244) -> getr Rx 13%bv = Z_to_bv 64 (w_sp w + 272) ->
                getr Rx 1%bv = Z_to_bv 64 0x679b8 ->
                getr Rx 21%bv = Z_to_bv 64 3 -> getr Rx 23%bv = Z_to_bv 64 (i_io I) -> getr Rx 25%bv = Z_to_bv 64 (i_op I) ->
                srealizes SEGS (cfg fx Rx (hc_emplace_u32 HConstsS1.hc) M2 model) K).
      { intros Rx vs ORx X18 Rvs X10 X11 X13 X1r X21 X23 X25.
        pose proof ORx as ORx'. destruct ORx' as (Ysp & Ygp & Ytp & Ys0 & _).
        pose proof Hn as Hn'. unfold PmLoopS1.nodes in Hn'.
        eapply (pm_emplace_m1 w c0 K fx A M2 model c Rx wv (w_sp w + 244) (w_sp w + 272) 0x679b8 PS FZ X2 Htr BUD MAC ltac:(pose proof (proj1 AACC eq_refl); lia)
                  ltac:(split; [exact X1r | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [exact Ysp | split; [exact Ygp | exact Ytp]]]]])
                  X10 X11 X13 C244_2 Ctup ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia) ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)).
        intros fx' A' R' M' model' p v m1' FZ' X' BUD' MAC' LEN KEPT Hpr Hin Rv AG'.
        pose proof (oregs_kept w Rx R' ORx KEPT) as OR'. pose proof (x_ai X') as AI'. pose proof (x_ms X') as MS'.
        keptQ KEPT X18 Y18. keptQ KEPT X21 Y21. keptQ KEPT X23 Y23. keptQ KEPT X25 Y25. pose proof OR' as OR''. destruct OR'' as (Ysp' & _ & _ & Ys0' & _).
        clear KEPT.

        pose proof (x_m1 X') as U'. cbn [set_m1 c_m1 t3a t3b t3c fst snd] in U'. destruct m1' as [[bl' bc'] ents']. cbn [t3a t3b t3c fst snd] in U', Hin, LEN.
        pose proof U' as U0. destruct U0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ Unode' _].
        destruct (Unode' p wv v Hin) as (Hlive & Hq0 & Hq47 & Hqal & _).
        destruct (ai_live_block MI A' M' model' p 24 AI' Hlive) as (_ & _ & _ & Hpc & _).
        pose proof (live_mdef SEGS Ly.L MI A' M' model' p 24 AI' Hlive) as HDp.
        destruct (in_split _ _ Hin) as (l1 & l2 & Eents).

        pm_seed R' w c [Z_to_bv 64 p; Z_to_bv 64 (PrsGrammar.sx32 vs)].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (18%bv, EVar 40)] R'. seedHK HK w A' M' model' (set_m1 c (bl', bc', ents')) E X'.
        apply (know_more E M' [KWr (SA (EVar 39) 20) (ELit 4)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil. eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact HDp | lia | lia] | lia | lia | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R' R5 OR' GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
        rewrite ?w_add by lia. rewrite PmBody1S1.w2lb4_sx32 by lia.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
        assert (ST3 : stores_in (zwin (p + 20) (p + 24)) M' M3) by (unfold M3; stin).
        pose proof (pm_m1_setval w A' M' model' (set_m1 c (bl', bc', ents')) l1 l2 p wv v vs X' ltac:(cbn; exact Eents) Rvs) as X3.
        cbn [set_m1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr c_widx c_icount c_endian c_reqconv t3a t3b t3c fst snd] in X3. fold M3 in X3.
        assert (AG3 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880) M2 M3).
        { intros a Ha. rewrite <- (AG' a ltac:(unfold w_sp0, PM_FRAME; lia)). apply (proj1 ST3). rewrite u64_of_Z by lia. unfold zwin. lia. }
        assert (Elen : Zlen (l1 ++ (p, (wv, vs)) :: l2) = Zlen ents') by (rewrite Eents; unfold Zlen; rewrite !length_app; reflexivity).
        assert (AGf : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880) M' M3).
        { eapply stores_in_agree; [exact ST3 | intros b0 Hb0; unfold zwin; lia]. }
        assert (AG23 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880) M2 M3).
        { intros a Ha. rewrite (AGf a Ha). apply AG'. unfold w_sp0, PM_FRAME. lia. }
        eapply (PK fx' FZ' A' M3 model' _ R5 1 []).
        + split; [exact X3|]. split; [exact Htr|]. split.
          { clear - BUD' Elen Eents. unfold pm_bud in BUD' |- *. cbn [set_m1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in BUD' |- *.
            unfold HRep.Zlength in *. unfold Zlen in Elen. rewrite !Elen. exact BUD'. }
          split; [exact OR5|].
          split; [eapply (PmBody1S1.loop_mem_frame w M2 M3); [exact LM2 | lia | lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]] |].
          split; [eapply (PmBody1S1.ictx_agree w M2 M3); [exact IC2 | lia | lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]] |].
          split; [eapply (ifr_agree w M2 M3); [exact FR2 | lia | lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]] |].
          cbn [c_icount c_endian c_v3 c_m1 c_m2 c_m3]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [| exact V3R].
          clear - MAC' Elen Eents. unfold PmLoopS1.macct in MAC' |- *. cbn [set_m1 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in MAC' |- *. unfold Zlen in *. rewrite !Elen. exact MAC'.
        + rewrite (GK5 21%bv) by (clear; cbn; tauto). exact Y21.
        + rewrite (GK5 23%bv) by (clear; cbn; tauto). exact Y23.
        + rewrite (GK5 25%bv) by (clear; cbn; tauto). exact Y25.
        + eapply (PmBody1S1.cellw_frame M2 M3); [exact C686_2 | lia | cbn; lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]].
        + left; lia.
        + reflexivity. + reflexivity. + reflexivity.
        + unfold PmLoopS1.nodes. cbn [set_m1 c_m1 c_m2 c_m3 t3c snd]. unfold Zlen in *. rewrite ?Elen. cbn [t3c snd] in LEN. lia.
        + cbn [set_m1 c_v3]. rewrite app_nil_r. reflexivity.
        + exact seed_free_nil.
        + rewrite Zlen_nil. lia.
        + left; reflexivity.
        + reflexivity.
        + right. split; [reflexivity|]. cbn [set_m1 c_m1 t3c snd]. unfold Zlen in *. rewrite ?Elen. cbn [t3c snd] in LEN. lia.
        + left; reflexivity.
        + intros []. }

      pose proof (proj1 C244_2) as Rwv2.
      destruct b; cbn in Gb.
      +
        pm_seed R4 w c [Z_to_bv 64 wv].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 1)] R4. seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KWord (SA (EVar 32) 244) (N.to_nat 4) (EVar 39); KWord (SA (EVar 32) 80) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 96))]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [exact C244 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w M1 80); [exact LM1 | (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
        apply (know_more E M1 [KImg 0xecf20 0xecf28]) in HK. 2: { repeat apply Forall_cons; try apply Forall_nil. eapply (relro_kimg w); [exact X1 | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }

        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (13%bv) G13. rreg HRn (18%bv) G18b.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
        rewrite ?ext_val_sx4 in G18b by lia. rewrite ?w_add in G10, G11, G13 |- * by lia. fold M2. change 433692 with (hc_emplace_u32 HConstsS1.hc).
        apply (TAILE R5 wv OR5 G18b ltac:(lia) ltac:(unfold O_M1; exact G10) G11 G13 G1);
          [rewrite (GK5 21%bv) by (clear; cbn; tauto) | rewrite (GK5 23%bv) by (clear; cbn; tauto) | rewrite (GK5 25%bv) by (clear; cbn; tauto)];
          first [rewrite (GK4 21%bv) by (clear; cbn; tauto); exact Q21b | rewrite (GK4 23%bv) by (clear; cbn; tauto); exact Q23b | rewrite (GK4 25%bv) by (clear; cbn; tauto); exact Q25b].
      +
        pm_seed R4 w c [Z_to_bv 64 tid].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R4. seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KWord (SA (EVar 32) 240) (N.to_nat 4) (EVar 39); KWord (SA (EVar 32) 80) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 96))]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [exact Ctid | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w M1 80); [exact LM1 | (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
        apply (know_more E M1 [KImg 0xecf20 0xecf28]) in HK. 2: { repeat apply Forall_cons; try apply Forall_nil. eapply (relro_kimg w); [exact X1 | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (13%bv) G13. rreg HRn (18%bv) G18b.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        pose proof (syms_id_sound _ _ _ _ [21; 23; 25]%bv HRn eq_refl) as GK5.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
        rewrite ?ext_val_sx4 in G18b by lia. rewrite ?w_add in G10, G11, G13 |- * by lia. fold M2. change 433692 with (hc_emplace_u32 HConstsS1.hc).
        apply (TAILE R5 tid OR5 G18b ltac:(lia) ltac:(unfold O_M1; exact G10) G11 G13 G1);
          [rewrite (GK5 21%bv) by (clear; cbn; tauto) | rewrite (GK5 23%bv) by (clear; cbn; tauto) | rewrite (GK5 25%bv) by (clear; cbn; tauto)];
          first [rewrite (GK4 21%bv) by (clear; cbn; tauto); exact Q21b | rewrite (GK4 23%bv) by (clear; cbn; tauto); exact Q23b | rewrite (GK4 25%bv) by (clear; cbn; tauto); exact Q25b].
  Qed.
End PM.
