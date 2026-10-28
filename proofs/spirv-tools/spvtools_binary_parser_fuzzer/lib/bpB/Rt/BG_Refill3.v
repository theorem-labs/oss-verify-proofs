(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BazyRestrict BazyLedger BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BazyMadvise.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepX BW_Efs BW_Populate BG_WFHit BG_RefillModel BS_Refill1 BecLazy.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma in_rangesb_subtract_false : forall x C l h, entries_nowrap C -> 0 <= l -> l <= h ->
  in_rangesb x C = false -> in_rangesb x (maps_subtract C l h) = false.
Proof. intros x C l h NW Hl Hh F. rewrite in_rangesb_zcovb, (zcovb_maps_subtract C l h _ NW Hl Hh). rewrite <- in_rangesb_zcovb, F. reflexivity. Qed.
Lemma in_rangesb_subtract_inside : forall x C l h, entries_nowrap C -> 0 <= l -> l <= h ->
  l <= bv_unsigned x < h -> in_rangesb x (maps_subtract C l h) = false.
Proof.
  intros x C l h NW Hl Hh R. rewrite in_rangesb_zcovb, (zcovb_maps_subtract C l h _ NW Hl Hh). unfold zinb.
  destruct (zcovb C (bv_unsigned x)); [| reflexivity]. cbn [andb].
  destruct (Z.leb_spec l (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) h); cbn; try reflexivity; lia.
Qed.
Lemma in_rangesb_subtract_true : forall x C l h, entries_nowrap C -> 0 <= l -> l <= h ->
  in_rangesb x (maps_subtract C l h) = true -> in_rangesb x C = true.
Proof.
  intros x C l h NW Hl Hh T. rewrite in_rangesb_zcovb, (zcovb_maps_subtract C l h _ NW Hl Hh) in T. rewrite in_rangesb_zcovb.
  destruct (zcovb C (bv_unsigned x)); [reflexivity| discriminate T].
Qed.
Lemma in_rangesb_subtract_keep : forall x C l h, entries_nowrap C -> 0 <= l -> l <= h ->
  in_rangesb x C = true -> (bv_unsigned x < l \/ h <= bv_unsigned x) -> in_rangesb x (maps_subtract C l h) = true.
Proof.
  intros x C l h NW Hl Hh T R. rewrite in_rangesb_zcovb, (zcovb_maps_subtract C l h _ NW Hl Hh). rewrite <- in_rangesb_zcovb, T. unfold zinb.
  destruct (Z.leb_spec l (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) h); cbn; try reflexivity; lia.
Qed.

Section AmodelAfterRefill.
  Variables (s : ast) (mo mo' : Model) (c : Z) (L' S' : list (word * word)) (AL2 : Z).
  Let st := a_st s.
  Let sb := a_sb s.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c. Let csz := class_size c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let s2 := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L' S' (a_Zr s) AL2 (a_top s) (a_bot s).
  Let h := m_vmmaps mo.
  Let h' := m_vmmaps mo'.

  Hypothesis AMX : AMODELX s mo.
  Hypothesis OK : ast_ok s.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis EMPTY : pc_count (get_pc st c) = 0.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis LNW : entries_nowrap (a_L s).

  Hypothesis EL : L' = (if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
                       else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s)).
  Hypothesis ES : S' = (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
                       ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Hypothesis VMM : vm_maps h' = vm_maps h.
  Hypothesis VMR : vm_reserved h' = vm_reserved h.
  Hypothesis VML : vm_limit h' = vm_limit h.
  Hypothesis VMB : vm_mmap_base h' = vm_mmap_base h.
  Hypothesis VMT : alloc_top h' = alloc_top h.
  Hypothesis VMN : vm_noaccess h' = (if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (vm_noaccess h) (RB s c + mu) (RB s c + mu') else vm_noaccess h) (FA s c + mfa) (FA s c + mfa')
                                    else (if mu <? mu' then maps_subtract (vm_noaccess h) (RB s c + mu) (RB s c + mu') else vm_noaccess h)).
  Hypothesis EAG : eager_used mo' <= eager_used mo + (mu' - mu) + (mfa' - mfa).

  Hypothesis HAL : 0 <= AL2 <= a_AL s.

  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let RF := rf_facts st c WFs HC ROOM.

  Let B : 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
          /\ 0 <= au <= mu /\ mu <= mu' <= mu + 262144 /\ mu' + 262144 <= 3758096384 /\ 0 <= mfa /\ mfa <= mfa' <= 536870912 /\ 1 <= c <= 30
          /\ 8 * ((mu' - mu) / 8) = mu' - mu /\ 8 * ((mfa' - mfa) / 8) = mfa' - mfa /\ (RB s c + mu) mod 8 = 0 /\ (FA s c + mfa) mod 8 = 0
          /\ RB s c mod 8 = 0 /\ mu mod 8 = 0 /\ mfa mod 8 = 0 /\ mfa' <= mfa + 262144.
  Proof.
    pose proof (rf_mfa_delta st c WFs HC ROOM) as FD.
    pose proof PL as (Y1 & Y2 & Y3 & _).
    destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    pose proof (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as RO.
    pose proof (ro_alloc_nonneg _ _ RO) as A1. pose proof (ro_alloc_le _ _ RO) as A2. pose proof (ro_mapped_mod _ _ RO) as A3.
    pose proof (ro_fa_le _ _ RO) as F1. pose proof (ro_fa_mod _ _ RO) as F2. pose proof (ro_numfreed _ _ RO) as F3.
    assert (ERB : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (EFA : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
    subst n csz nf mfa au mu nf1 mfa' au' mu' r st sb. unfold a_sb in *. unfold zlen in F3.
    set (MU' := rf_mu' _ _ _ _) in *. set (MFA' := rf_mfa' _ _ _ _ _) in *. set (MU := rg_mapped_user _) in *. set (MFA := rg_mapped_free_array _) in *.
    set (AU := rg_allocated_user _) in *. set (SB := as_space_beg _) in *.
    assert (M : 8 * ((MU' - MU) / 8) = MU' - MU /\ 8 * ((MFA' - MFA) / 8) = MFA' - MFA /\ (RB s c + MU) mod 8 = 0 /\ (FA s c + MFA) mod 8 = 0
                /\ RB s c mod 8 = 0 /\ MU mod 8 = 0 /\ MFA mod 8 = 0).
    { rewrite EFA, ERB. clear - Q8 Q13 A3 F2 Y1; try acb. Z.div_mod_to_equations. lia. }
    clear - Y2 Y3 ERB EFA A1 A2 Q7 ROOM F1 F3 Q12 HC M FD; try acb. repeat split; try lia.
  Qed.

  Theorem amodelx_after_refill : AMODELX s2 mo'.
  Proof.
    destruct AMX as [[AIL [ASV ABU]] AK]. pose proof B as (B1 & B2 & ERB & EFA & B5 & B6 & B7 & B8 & B9 & B10 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
    assert (NUM := conj B1 (conj B2 (conj ERB (conj EFA (conj B5 (conj B6 (conj B7 (conj B8 (conj B9 (conj B10 M8)))))))))).
    destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    pose proof AK as (K1 & K2 & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11).

    set (subU := fun X : list (word * word) => if mu <? mu' then maps_subtract X (RB s c + mu) (RB s c + mu') else X).
    set (subF := fun X : list (word * word) => if mfa <? mfa' then maps_subtract X (FA s c + mfa) (FA s c + mfa') else X).
    assert (ELs : L' = subF (subU (a_L s))) by (rewrite EL; subst subU subF; destruct (mfa <? mfa'); destruct (mu <? mu'); reflexivity).
    assert (ENs : vm_noaccess h' = subF (subU (vm_noaccess h))) by (rewrite VMN; subst subU subF; destruct (mfa <? mfa'); destruct (mu <? mu'); reflexivity).
    assert (NWU : forall X, entries_nowrap X -> entries_nowrap (subU X)).
    { intros X HX. subst subU. destruct (mu <? mu'); [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| exact HX]. }
    assert (NWF : forall X, entries_nowrap X -> entries_nowrap (subF X)).
    { intros X HX. subst subF. destruct (mfa <? mfa'); [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| exact HX]. }
    assert (SUBf : forall X x, entries_nowrap X -> in_rangesb x X = false -> in_rangesb x (subF (subU X)) = false).
    { intros X x HX F. subst subU subF. destruct (mfa <? mfa'); destruct (mu <? mu');
        repeat (apply in_rangesb_subtract_false; [first [apply maps_subtract_nowrap| idtac]; try exact HX; clear - NUM; try acb; lia| clear - NUM; try acb; lia| clear - NUM; try acb; lia|]); exact F. }
    assert (SUBt : forall X x, entries_nowrap X -> in_rangesb x (subF (subU X)) = true -> in_rangesb x X = true).
    { intros X x HX T. subst subU subF. destruct (mfa <? mfa'); destruct (mu <? mu'); try exact T.
      - apply (in_rangesb_subtract_true x X (RB s c + mu) (RB s c + mu')); [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia|].
        apply (in_rangesb_subtract_true x _ (FA s c + mfa) (FA s c + mfa')); [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact T].
      - apply (in_rangesb_subtract_true x X (FA s c + mfa) (FA s c + mfa')); [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact T].
      - apply (in_rangesb_subtract_true x X (RB s c + mu) (RB s c + mu')); [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact T]. }
    assert (SUBu : forall X x, entries_nowrap X -> mu < mu' -> RB s c + mu <= bv_unsigned x < RB s c + mu' -> in_rangesb x (subF (subU X)) = false).
    { intros X x HX LT R. subst subU subF. rewrite (proj2 (Z.ltb_lt _ _) LT).
      assert (F0 : in_rangesb x (maps_subtract X (RB s c + mu) (RB s c + mu')) = false)
        by (apply in_rangesb_subtract_inside; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact R]).
      destruct (mfa <? mfa'); [| exact F0].
      apply in_rangesb_subtract_false; [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact F0]. }
    assert (SUBfa : forall X x, entries_nowrap X -> mfa < mfa' -> FA s c + mfa <= bv_unsigned x < FA s c + mfa' -> in_rangesb x (subF (subU X)) = false).
    { intros X x HX LT R. subst subF. rewrite (proj2 (Z.ltb_lt _ _) LT).
      apply in_rangesb_subtract_inside; [apply NWU; exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact R]. }

    assert (SMONO : forall x, in_rangesb x (a_S s) = true -> in_rangesb x S' = true).
    { intros x T. rewrite ES, !in_rangesb_app, T, !Bool.orb_true_r. reflexivity. }
    split; [split; [| split]|].
    -
      unfold amaps_in_ledger. change (a_st s2) with st2. change (a_L s2) with L'. fold h'. rewrite VMM, ENs, ELs.
      assert (MAPS2 : forall mp, In mp (as_maps st2) ->
                In mp (as_maps st) \/ (mfa < mfa' /\ mp = mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false)
                                   \/ (mu < mu' /\ mp = mkMap (RB s c + mu) (mu' - mu) (MkUserMap c) PROT_RW false)).
      { intros mp Hin. unfold st2, refilled in Hin. cbn [as_maps] in Hin. unfold refill_newmaps in Hin.
        fold st r nf mfa au mu in Hin. fold mu' mfa' in Hin. change (free_array_base st c) with (FA s c) in Hin. change (region_beg st c) with (RB s c) in Hin.
        apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [| left; exact Hin].
        apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
        - destruct (Z.ltb_spec mfa mfa'); [| destruct Hin]. destruct Hin as [<-|[]]. right; left. split; [assumption| reflexivity].
        - destruct (Z.ltb_spec mu mu'); [| destruct Hin]. destruct Hin as [<-|[]]. right; right. split; [assumption| reflexivity]. }
      split.
      { intros mp Hin K1' K2' K3' K4'. destruct (MAPS2 mp Hin) as [Hin'|[[_ ->]|[_ ->]]].
        - exact (IL1 mp Hin' K1' K2' K3' K4').
        - exfalso. exact (proj2 (K2' c) eq_refl).
        - exfalso. exact (proj1 (K2' c) eq_refl). }
      split.
      { intros mp Hin KD x Hx. destruct (MAPS2 mp Hin) as [Hin'|[[LT ->]|[LT ->]]].
        - destruct (IL2 mp Hin' KD x Hx) as [F1 F2]. split; [apply SUBf; [exact NWA| exact F1]| apply SUBf; [exact LNW| exact F2]].
        - cbn [mp_base mp_size] in Hx. split; [apply SUBfa; [exact NWA| exact LT| clear - Hx; try acb; lia]| apply SUBfa; [exact LNW| exact LT| clear - Hx; try acb; lia]].
        - cbn [mp_base mp_size] in Hx. split; [apply SUBu; [exact NWA| exact LT| clear - Hx; try acb; lia]| apply SUBu; [exact LNW| exact LT| clear - Hx; try acb; lia]]. }
      split.
      { intros sc x Hsc Hx. change (as_sec st2) with (as_sec st) in Hsc. apply SUBf; [exact LNW| exact (IL3 sc x Hsc Hx)]. }
      split; [exact NOV|]. split; [exact NW|]. apply NWF, NWU. exact NWA.
    -
      unfold ashadow_visible. change (a_st s2) with st2. change (a_S s2) with S'. destruct ASV as [V1 V2]. split.
      + intros c0 x Hc0 Hx. change (RB s2 c0) with (RB s c0) in Hx. unfold st2 in Hx.
        destruct (Z.eq_dec c0 c) as [->|NE].
        * rewrite (rfd_region_c st c WFs HC ROOM) in Hx. cbn [rg_mapped_user refill_region] in Hx. fold st r nf au mu in Hx. fold mu' in Hx.
          destruct (Z.lt_ge_cases (bv_unsigned x) (sh (RB s c) + mu / 8)) as [LO|HI].
          -- apply SMONO. apply (V1 c x Hc0). change (rg_mapped_user (get_region (a_st s) c)) with mu. clear - Hx LO; try acb. lia.
          -- rewrite ES, !in_rangesb_app.
             assert (LT : mu < mu') by (clear - Hx HI M3 NUM; try acb; unfold sh in *; Z.div_mod_to_equations; lia).
             rewrite (proj2 (Z.ltb_lt _ _) LT). cbn [in_rangesb existsb app]. unfold zin_rangeb. cbn [fst snd]. unfold wz.
             rewrite (unsigned_lit (sh (RB s c + mu))) by (unfold sh, ASHADOW_BASE; clear - NUM; try acb; Z.div_mod_to_equations; lia).
             rewrite (unsigned_lit ((mu' - mu) / 8)) by (clear - NUM; try acb; Z.div_mod_to_equations; lia).
             replace ((sh (RB s c + mu) <=? bv_unsigned x) && (bv_unsigned x <? sh (RB s c + mu) + (mu' - mu) / 8)) with true; [rewrite !Bool.orb_true_r, ?Bool.orb_true_l; destruct (mfa <? mfa'); reflexivity|].
             symmetry. apply andb_true_intro. unfold sh in *. split; [apply Z.leb_le| apply Z.ltb_lt]; clear - Hx HI M1 M3 M5 M6 NUM; try acb; Z.div_mod_to_equations; lia.
        * rewrite (rfd_region_o st c WFs HC ROOM c0) in Hx by (clear - Hc0 NE; try acb; unfold kNumClasses in Hc0; lia). apply SMONO. exact (V1 c0 x Hc0 Hx).
      + intros sc x Hsc Hx. change (as_sec st2) with (as_sec st) in Hsc. apply SMONO. exact (V2 sc x Hsc Hx).
    -
      unfold ABUDGET in ABU |- *. change (a_AL s2) with AL2. change (a_S s2) with S'.
      assert (GR : mu mod 262144 = 0 /\ mfa mod 262144 = 0 /\ (mu' - mu) mod 262144 = 0 /\ (mfa' - mfa) mod 262144 = 0).
      { destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
        pose proof (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as RO.
        pose proof (ro_mapped_mod _ _ RO) as MM. pose proof (ro_fa_mod _ _ RO) as FM.
        clear - Q7 Q8 Q12 Q13 MM FM NUM. unfold kUserMapSize, kFreeArrayMapSize, kFreeArraySize in *.
        repeat match goal with x := _ |- _ => subst x end.
        set (MU' := rf_mu' _ _ _ _) in *. set (MFA' := rf_mfa' _ _ _ _ _) in *. set (MU := rg_mapped_user _) in *. set (MFA := rg_mapped_free_array _) in *.
        Z.div_mod_to_equations. lia. }
      destruct GR as (GR1 & GR2 & GR3 & GR4).
      assert (PHI : aPhi s2 = aPhi s - ((mu' - mu) + (mfa' - mfa) + 40960 * ((mu' - mu) / 262144 + (mfa' - mfa) / 262144))).
      { unfold aPhi. change (a_st s2) with st2. change (a_st s) with st.
        assert (RC : get_region st2 c = refill_region st c) by (unfold st2; apply rfd_region_c; [exact WFs| exact HC| exact ROOM]).
        rewrite (pusage_grow st st2 c ltac:(clear - HC; lia)).
        - rewrite RC. cbn [rg_mapped_user rg_mapped_free_array refill_region].
          change (rf_mu' c (rg_num_freed (get_region st c)) (rg_allocated_user (get_region st c)) (rg_mapped_user (get_region st c))) with mu'.
          change (rf_mfa' c (rg_num_freed (get_region st c)) (rg_mapped_free_array (get_region st c)) (rg_allocated_user (get_region st c)) (rg_mapped_user (get_region st c))) with mfa'.
          change (rg_mapped_user (get_region st c)) with mu. change (rg_mapped_free_array (get_region st c)) with mfa. clear; lia.
        - intros c' Hc' NE. unfold st2. rewrite (rfd_region_o st c WFs HC ROOM c') by (clear - Hc' NE; lia). split; reflexivity.
        - exact GR1.
        - exact GR2.
        - rewrite RC. exact GR3.
        - rewrite RC. exact GR4.
        - rewrite RC. exact (proj1 B6).
        - rewrite RC. exact (proj1 B9).
      }
      rewrite PHI. fold h'. rewrite VML.
      destruct ABU as [AB0 AB1]. destruct HAL as [H0 H1].
      assert (KU : (mu <? mu') = true -> (mu' - mu) / 262144 = 1).
      { intros LT. apply Z.ltb_lt in LT. clear - LT GR3 NUM. Z.div_mod_to_equations. lia. }
      assert (KF : (mfa <? mfa') = true -> (mfa' - mfa) / 262144 = 1).
      { intros LT. apply Z.ltb_lt in LT. clear - LT GR4 NUM. Z.div_mod_to_equations. lia. }
      assert (K0 : 0 <= (mu' - mu) / 262144 /\ 0 <= (mfa' - mfa) / 262144) by (clear - NUM; split; apply Z.div_pos; lia).
      assert (PT : pages_total S' <= pages_total (a_S s) + 10 * ((mu' - mu) / 262144 + (mfa' - mfa) / 262144)).
      { rewrite ES, !pages_total_app.
        assert (W1 : pages_total (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else []) <= 10 * ((mfa' - mfa) / 262144)).
        { destruct (mfa <? mfa'); [rewrite (KF eq_refl)| cbn; clear -K0; lia]. rewrite pages_total_cons. cbn [pages_total].
          pose proof (cl_bounds (wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))) as CB. cbn [fst snd] in CB. unfold wz in CB.
          rewrite (unsigned_lit ((mfa' - mfa) / 8)) in CB by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold page_size in CB.
          assert (DV : (mfa' - mfa) / 8 / 4096 <= 8) by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold wz. clear - CB DV; try acb. lia. }
        assert (W2 : pages_total (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) <= 10 * ((mu' - mu) / 262144)).
        { destruct (mu <? mu'); [rewrite (KU eq_refl)| cbn; clear -K0; lia]. rewrite pages_total_cons. cbn [pages_total].
          pose proof (cl_bounds (wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))) as CB. cbn [fst snd] in CB. unfold wz in CB.
          rewrite (unsigned_lit ((mu' - mu) / 8)) in CB by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold page_size in CB.
          assert (DV : (mu' - mu) / 8 / 4096 <= 8) by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold wz. clear - CB DV; try acb. lia. }
        clear - W1 W2; try acb. lia. }
      unfold page_size in *. clear - AB1 H0 H1 PT EAG NUM K0; try acb. unfold h. lia.
    -
      unfold akernel. fold h'. rewrite VMR, VML, VMT, VMM, ENs. change (a_thr s2) with (a_thr s). change (a_ctx s2) with (a_ctx s). change (a_sb s2) with (a_sb s).
      change (a_pa s2) with (a_pa s). change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L'. change (as_sec (a_st s2)) with (as_sec st).
      replace (RB s2) with (RB s) by reflexivity. rewrite ELs.
      split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4a|]. split; [exact K4b|]. split; [exact K4c|]. split; [exact K5a|]. split; [exact K5b|].
      split.
      { intros x Hx. destruct (K5c x Hx) as [Z1 Z2]. split; [exact Z1|].
        pose proof sh_ceiling_lt_AHI_LO as SC. unfold AHI_LO in *.
        subst subU subF. destruct (mfa <? mfa'); destruct (mu <? mu').
        - apply in_rangesb_subtract_keep; [apply maps_subtract_nowrap; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| | clear - Hx SC NUM; try acb; lia].
          apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx SC NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx SC NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx SC NUM; try acb; lia].
        - exact Z2. }
      split; [intros x Hx; apply K6a; apply (SUBt _ x NWA Hx)|].
      split; [intros sc x Hsc Hx; apply (SUBf _ x NWA); exact (K6b sc x Hsc Hx)|].
      split; [exact K7|]. split; [exact K8a|]. split; [exact K8b|].
      split; [| split; [exact K9| split; [exact K10|]]].
      2:{
          intros xa xn HB. pose proof (K11 xa xn HB) as FR0.
          assert (FRU : region_free (subU (vm_noaccess h)) xa xn = true) by (subst subU; cbv beta; destruct (mu <? mu'); [apply BazyMadvise.region_free_maps_subtract; [exact NWA| exact FR0]| exact FR0]).
          pose proof (NWU _ NWA) as NWU0. subst subF. cbv beta. destruct (mfa <? mfa'); [apply BazyMadvise.region_free_maps_subtract; [exact NWU0| exact FRU]| exact FRU]. }
      {
        intros x Hx. destruct (K8c x Hx) as [Z1 Z2]. split; [exact Z1|].
        unfold sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in Hx.
        destruct (mfa <? mfa'); destruct (mu <? mu').
        - apply in_rangesb_subtract_keep; [apply maps_subtract_nowrap; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| | clear - Hx NUM; try acb; lia].
          apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx NUM; try acb; lia].
        - exact Z2. }
  Qed.
End AmodelAfterRefill.

End HCW.

