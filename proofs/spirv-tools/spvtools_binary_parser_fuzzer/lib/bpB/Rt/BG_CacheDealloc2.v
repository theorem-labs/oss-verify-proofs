(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BAllocSim BMmapSim BazyRestrict BazyLedger BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BazyMadvise.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepX BW_Efs BS_Rta BG_Refill3 BG_RepQ.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section CDModel.
  Variables (s : ast) (mo mo' : Model) (XC XB : list Z) (c : Z) (st' : astate) (L' S' : list (word * word)) (AL2 k mfa' : Z) (fl' : list Z).
  Let st := a_st s.
  Let sb := a_sb s.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r.
  Let nf' := nf + k.
  Let s2 := mkAst st' (a_thr s) (a_ctx s) (a_fsb s) L' S' (a_Zr s) AL2 (a_top s) (a_bot s).
  Let h := m_vmmaps mo.
  Let h' := m_vmmaps mo'.

  Hypothesis AMX : AMODELX s mo.
  Hypothesis PL : placed_ok s.
  Hypothesis WQ : WFQ st XC XB.
  Hypothesis HC : 1 <= c <= 30.

  Hypothesis KR : (k = 0 /\ mfa' = mfa) \/ (k = max_count c / 2 /\ mfa' = rta_mfa nf k mfa).
  Hypothesis FROOM : mfa' <= kFreeArraySize.

  Hypothesis Fsb : as_space_beg st' = as_space_beg st. Hypothesis Fpa : as_ptr_array st' = as_ptr_array st.
  Hypothesis Fsec : as_sec st' = as_sec st.
  Hypothesis Frg_c : get_region st' c = mkRegion mu au nf' fl' mfa'.
  Hypothesis Frg_o : forall c0, 0 <= c0 -> c0 <> c -> get_region st' c0 = get_region st c0.
  Hypothesis Fmaps : as_maps st' = (if mfa <? mfa' then [mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false] else []) ++ as_maps st.
  Hypothesis LNW : entries_nowrap (a_L s).

  Hypothesis EL : L' = (if mfa <? mfa' then maps_subtract (a_L s) (FA s c + mfa) (FA s c + mfa') else a_L s).
  Hypothesis ES : S' = (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else []) ++ a_S s.
  Hypothesis VMM : vm_maps h' = vm_maps h.
  Hypothesis VMR : vm_reserved h' = vm_reserved h.
  Hypothesis VML : vm_limit h' = vm_limit h.
  Hypothesis VMB : vm_mmap_base h' = vm_mmap_base h.
  Hypothesis VMT : alloc_top h' = alloc_top h.
  Hypothesis VMN : vm_noaccess h' = (if mfa <? mfa' then maps_subtract (vm_noaccess h) (FA s c + mfa) (FA s c + mfa') else vm_noaccess h).
  Hypothesis EAG : eager_used mo' <= eager_used mo + (mfa' - mfa).
  Hypothesis HAL : 0 <= AL2 <= a_AL s.

  Let RO : region_ok st c. Proof. exact (WFQ_region st _ _ c WQ ltac:(clear - HC; unfold kNumClasses; lia)). Qed.

  Let B : 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
          /\ 0 <= mfa /\ mfa <= mfa' <= 536870912 /\ 1 <= c <= 30
          /\ 8 * ((mfa' - mfa) / 8) = mfa' - mfa /\ (FA s c + mfa) mod 8 = 0 /\ mfa mod 262144 = 0 /\ (mfa' - mfa) mod 262144 = 0 /\ mfa' <= mfa + 262144
          /\ mu mod 262144 = 0.
  Proof.
    clear AMX Fsb Fpa Fsec Frg_c Frg_o Fmaps LNW EL ES VMM VMR VML VMB VMT VMN EAG HAL.
    pose proof PL as (Y1 & Y2 & Y3 & _). fold sb in Y1, Y2, Y3.
    pose proof (ro_fa_le _ _ RO) as F1. pose proof (ro_fa_mod _ _ RO) as F2. pose proof (ro_numfreed _ _ RO) as F3. pose proof (ro_mapped_mod _ _ RO) as F4.
    fold st r nf mfa mu in F1, F2, F3, F4. unfold zlen in F3.
    assert (ERB : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (EFA : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    pose proof (class_size_table_facts c ltac:(clear - HC; lia)) as (_ & _ & _ & C4 & C5 & C6).
    unfold AHI_LO, kSpaceSize, kPageSize, kFreeArraySize, kFreeArrayMapSize, kUserMapSize in *.
    assert (M : mfa <= mfa' /\ (mfa' - mfa) mod 262144 = 0 /\ mfa' <= mfa + 262144).
    { destruct KR as [(_ & ->)|(-> & ->)]; [clear; Z.div_mod_to_equations; lia|].
      unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize. destruct (Z.leb_spec (4 * (nf + max_count c / 2)) mfa) as [LE|GT]; [clear; Z.div_mod_to_equations; lia|].
      clear - GT F1 F2 F3 C4 C5 C6. Z.div_mod_to_equations. lia. }
    clear - Y1 Y2 Y3 ERB EFA F1 F2 F3 F4 M FROOM HC. acb. Z.div_mod_to_equations. repeat split; lia.
  Qed.

  Theorem amodelx_after_cd : AMODELX s2 mo'.
  Proof.
    destruct AMX as [[AIL [ASV ABU]] AK]. pose proof B as (B1 & B2 & ERB & EFA & B5 & B6 & B7 & M1 & M2 & M3 & M4 & M5 & M6).
    assert (NUM := conj B1 (conj B2 (conj ERB (conj EFA (conj B5 (conj B6 (conj B7 M5))))))).
    destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    pose proof AK as (K1 & K2 & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11).
    set (subF := fun X : list (word * word) => if mfa <? mfa' then maps_subtract X (FA s c + mfa) (FA s c + mfa') else X).
    assert (ELs : L' = subF (a_L s)) by (rewrite EL; subst subF; reflexivity).
    assert (ENs : vm_noaccess h' = subF (vm_noaccess h)) by (rewrite VMN; subst subF; reflexivity).
    assert (NWF : forall X, entries_nowrap X -> entries_nowrap (subF X)).
    { intros X HX. subst subF. destruct (mfa <? mfa'); [apply maps_subtract_nowrap; [exact HX| clear - NUM; lia| clear - NUM; lia]| exact HX]. }
    assert (SUBf : forall X x, entries_nowrap X -> in_rangesb x X = false -> in_rangesb x (subF X) = false).
    { intros X x HX F. subst subF. destruct (mfa <? mfa'); [| exact F].
      apply in_rangesb_subtract_false; [exact HX| clear - NUM; lia| clear - NUM; lia| exact F]. }
    assert (SUBt : forall X x, entries_nowrap X -> in_rangesb x (subF X) = true -> in_rangesb x X = true).
    { intros X x HX T. subst subF. destruct (mfa <? mfa'); [| exact T].
      apply (in_rangesb_subtract_true x X (FA s c + mfa) (FA s c + mfa')); [exact HX| clear - NUM; lia| clear - NUM; lia| exact T]. }
    assert (SUBfa : forall X x, entries_nowrap X -> mfa < mfa' -> FA s c + mfa <= bv_unsigned x < FA s c + mfa' -> in_rangesb x (subF X) = false).
    { intros X x HX LT R. subst subF. rewrite (proj2 (Z.ltb_lt _ _) LT).
      apply in_rangesb_subtract_inside; [exact HX| clear - NUM; lia| clear - NUM; lia| exact R]. }
    assert (SMONO : forall x, in_rangesb x (a_S s) = true -> in_rangesb x S' = true).
    { intros x T. rewrite ES, !in_rangesb_app, T, !Bool.orb_true_r. reflexivity. }
    assert (Es2 : a_sb s2 = a_sb s /\ a_pa s2 = a_pa s /\ (forall c0, RB s2 c0 = RB s c0)).
    { unfold a_sb, a_pa, RB, region_beg. cbn [a_st]. rewrite Fsb, Fpa. repeat split; reflexivity. }
    destruct Es2 as (Esb & Epa & ERB2).
    split; [split; [| split]|].
    -
      unfold amaps_in_ledger. change (a_st s2) with st'. change (a_L s2) with L'. fold h'. rewrite VMM, ENs, ELs, Fsec, Fmaps.
      assert (MAPS2 : forall mp, In mp ((if mfa <? mfa' then [mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false] else []) ++ as_maps st) ->
                In mp (as_maps st) \/ (mfa < mfa' /\ mp = mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false)).
      { intros mp Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [| left; exact Hin].
        destruct (Z.ltb_spec mfa mfa'); [| destruct Hin]. destruct Hin as [<-|[]]. right. split; [assumption| reflexivity]. }
      split.
      { intros mp Hin K1' K2' K3' K4'. destruct (MAPS2 mp Hin) as [Hin'|[_ ->]].
        - exact (IL1 mp Hin' K1' K2' K3' K4').
        - exfalso. exact (proj2 (K2' c) eq_refl). }
      split.
      { intros mp Hin KD x Hx. destruct (MAPS2 mp Hin) as [Hin'|[LT ->]].
        - destruct (IL2 mp Hin' KD x Hx) as [F1 F2]. split; [apply SUBf; [exact NWA| exact F1]| apply SUBf; [exact LNW| exact F2]].
        - cbn [mp_base mp_size] in Hx. split; [apply SUBfa; [exact NWA| exact LT| clear - Hx; lia]| apply SUBfa; [exact LNW| exact LT| clear - Hx; lia]]. }
      split.
      { intros sc x Hsc Hx. apply SUBf; [exact LNW| exact (IL3 sc x Hsc Hx)]. }
      split; [exact NOV|]. split; [exact NW|]. apply NWF. exact NWA.
    -
      unfold ashadow_visible. change (a_st s2) with st'. change (a_S s2) with S'. rewrite Fsec. destruct ASV as [V1 V2]. split.
      + intros c0 x Hc0 Hx. rewrite (ERB2 c0) in Hx. apply SMONO. apply (V1 c0 x Hc0).
        destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite Frg_c in Hx; cbn [rg_mapped_user] in Hx; exact Hx| rewrite (Frg_o c0 (proj1 Hc0) NE) in Hx; exact Hx].
      + intros sc x Hsc Hx. apply SMONO. exact (V2 sc x Hsc Hx).
    -
      unfold ABUDGET in ABU |- *. change (a_AL s2) with AL2. change (a_S s2) with S'.
      assert (PHI : aPhi s2 = aPhi s - ((mfa' - mfa) + 40960 * ((mfa' - mfa) / 262144))).
      { unfold aPhi. change (a_st s2) with st'. change (a_st s) with st.
        rewrite (pusage_grow st st' c ltac:(clear - HC; lia)).
        - rewrite Frg_c. cbn [rg_mapped_user rg_mapped_free_array]. fold r. fold mu mfa. rewrite Z.sub_diag. change (0 / 262144) with 0. clear; lia.
        - intros c' Hc' NE. rewrite (Frg_o c') by (clear - Hc' NE; lia). split; reflexivity.
        - fold r. fold mu. exact M6.
        - fold r. fold mfa. exact M3.
        - rewrite Frg_c. cbn [rg_mapped_user]. fold r. fold mu. rewrite Z.sub_diag. reflexivity.
        - rewrite Frg_c. cbn [rg_mapped_free_array]. fold r. fold mfa. exact M4.
        - rewrite Frg_c. cbn [rg_mapped_user]. fold r. fold mu. clear; lia.
        - rewrite Frg_c. cbn [rg_mapped_free_array]. fold r. fold mfa. clear - B6; lia. }
      rewrite PHI. fold h'. rewrite VML.
      destruct ABU as [AB0 AB1]. destruct HAL as [H0 H1].
      assert (KF : (mfa <? mfa') = true -> (mfa' - mfa) / 262144 = 1).
      { intros LT. apply Z.ltb_lt in LT. clear - LT M4 NUM. Z.div_mod_to_equations. lia. }
      assert (K0 : 0 <= (mfa' - mfa) / 262144) by (clear - NUM; apply Z.div_pos; lia).
      assert (PT : pages_total S' <= pages_total (a_S s) + 10 * ((mfa' - mfa) / 262144)).
      { rewrite ES, pages_total_app.
        assert (W1 : pages_total (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else []) <= 10 * ((mfa' - mfa) / 262144)).
        { destruct (mfa <? mfa'); [rewrite (KF eq_refl)| cbn; clear - K0; lia]. rewrite pages_total_cons. cbn [pages_total].
          pose proof (cl_bounds (wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))) as CB. cbn [fst snd] in CB. unfold wz in CB.
          rewrite (unsigned_lit ((mfa' - mfa) / 8)) in CB by (clear - NUM; Z.div_mod_to_equations; lia). unfold page_size in CB.
          assert (DV : (mfa' - mfa) / 8 / 4096 <= 8) by (clear - NUM; Z.div_mod_to_equations; lia). unfold wz. clear - CB DV. lia. }
        clear - W1. lia. }
      unfold page_size in *. clear - AB1 H0 H1 PT EAG NUM K0. unfold h. lia.
    -
      unfold akernel. unfold hsec in K10 |- *. fold h'. rewrite VMR, VML, VMT, VMM, ENs. change (a_thr s2) with (a_thr s). change (a_ctx s2) with (a_ctx s). rewrite Esb, Epa.
      change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L'. change (a_st s2) with st'. rewrite Fsec. rewrite ELs.
      split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      split; [intros a n c0 Hc0 Ha Hn; rewrite (ERB2 c0) in Ha, Hn; exact (K4a a n c0 Hc0 Ha Hn)|].
      split; [exact K4b|]. split; [exact K4c|]. split; [exact K5a|]. split; [exact K5b|].
      split.
      { intros x Hx. destruct (K5c x Hx) as [Z1 Z2]. split; [exact Z1|].
        pose proof sh_ceiling_lt_AHI_LO as SC. unfold AHI_LO in *. subst subF. destruct (mfa <? mfa'); [| exact Z2].
        apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; lia| clear - NUM; lia| exact Z2| clear - Hx SC NUM; lia]. }
      split; [intros x Hx; apply K6a; apply (SUBt _ x NWA Hx)|].
      split; [intros sc x Hsc Hx; apply (SUBf _ x NWA); exact (K6b sc x Hsc Hx)|].
      split; [exact K7|]. split; [exact K8a|]. split; [exact K8b|].
      split; [| split; [exact K9| split; [exact K10|]]].
      2:{
          intros xa xn HB. subst subF. cbv beta. destruct (mfa <? mfa'); [apply BazyMadvise.region_free_maps_subtract; [exact NWA|]|]; exact (K11 xa xn HB). }
      { intros x Hx. destruct (K8c x Hx) as [Z1 Z2]. split; [exact Z1|].
        unfold sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in Hx. subst subF. destruct (mfa <? mfa'); [| exact Z2].
        apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; lia| clear - NUM; lia| exact Z2| clear - Hx NUM; lia]. }
  Qed.
End CDModel.

End HCW.
