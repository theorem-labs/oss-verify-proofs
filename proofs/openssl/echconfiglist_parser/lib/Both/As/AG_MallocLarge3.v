(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require LazyMadvise.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepX AsDepotInv
     SecLazy SecLazy2 AS_AllocSec1 AG_LargeModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition lg_L (L : list (word * word)) (pa nres nch : Z) : list (word * word) :=
  if nch =? nres then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L.
(* [comment removed for export] *)
Definition lg_cost (msz : Z) : Z := msz + 0x20000 + (msz / 32768 + 2) * 4096.

Section ModelAfterLarge.
  Variables (s : ast) (mo mo2 : Model) (a size : Z) (d : depot).
  Let st := a_st s.
  Let pa := a_pa s.
  Let r := compute_req size.
  Let needed := rq_needed r.
  Let msz := round_up needed kPageSize + kPageSize.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let st2 := large_state st a size.
  Let Wsh : word * word := (wz (sh a), wz (msz / 8)).
  Let L2 := lg_L (a_L s) pa nres nch.
  Let AL2 := a_AL s - lg_cost msz.
  Let s2 := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 (Wsh :: a_S s) (a_Zr s) AL2 (a_top s) (a_bot s).

  Hypothesis AMX : AMODELX s mo.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis SZ : 64512 < size < 2^32.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0.
  Hypothesis FREE : region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true.
  Hypothesis LM : rsub (a_L s) (vm_maps (m_vmmaps mo)).         (* [comment removed for export] *)
  Hypothesis NWL : entries_nowrap (a_L s).                        (* [comment removed for export] *)
  Hypothesis ALLOW : lg_cost msz <= a_AL s.
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil.
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20.
  Hypothesis MO : as_model mo a msz pa nres (nch =? nres) mo2.

  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. pose proof (proj1 AR) as X. clear - X. aunf. lia. Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let RQ := large_req size SZ.

  Let GEO : size + 8 <= needed - 4088 /\ needed <= size + 4104 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ needed mod 8 = 0 /\ msz mod 4096 = 0 /\ a mod 4096 = 0.
  Proof.
    apply (large_geo st a size SZ). destruct AR as (_ & _ & AL). unfold kPageSize. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. exact AL.
  Qed.
  (* [comment removed for export] *)
  Let BND : 12599296 <= a /\ a + msz <= aceil /\ 73728 <= msz /\ 12599296 <= pa /\ pa + 8388608 <= aceil
            /\ 2148314624 <= sh a /\ sh a + msz / 8 <= (sh aceil) /\ 8 * (msz / 8) = msz.
  Proof.
    destruct AR as (A1 & A2 & A3). pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7). destruct PAR as [P1 P2].
    pose proof (aapp_sh_env_div _ _ A1 ltac:(clear - G1 G3 SZ; lia)) as ASH.
    apply aapp_env in A1; [| clear - G1 G3 SZ; lia]. apply aapp_env in P1; [| unfold kPtrArrayReserve; clear; lia].
    acb. unfold AHI_LO, kPtrArrayReserve in *. subst pa.
    unfold round_up, round_down, sh, ASHADOW_BASE in *. repeat split; try (first [clear - ARE AR SZ G1 G3 G5 G6 ACEILB PAE PAR ASH; lia | lia]); Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Let PBAND : pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa.
  Proof. pose proof (aapp_lit _ _ (proj1 PAR)) as L. unfold kPtrArrayReserve in L. exact L. Qed.

  Theorem amodelx_after : AMODELX s2 mo2 /\ depot_cov d mo2.
  Proof.
    destruct AMX as [AM AK]. destruct AM as (AIL & ASV & AB). destruct AIL as (A1 & A2 & A3 & NOV & NW & NWA).
    pose proof MO as M; unfold as_model in M; cbv beta iota zeta in M. destruct M as (NV & VM2 & VR2 & VL2 & VB2 & VK2 & VS2 & VA2 & EAG2).
    pose proof BND as B. destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). acb. pose proof PBAND as PB'.
    assert (SHLO : sh AHI_LO = 0x2008fff7000) by (rewrite <- AHSB_eq; reflexivity). pose proof sh_ceiling_range as SCV.   (* [comment removed for export] *)
    set (h := m_vmmaps mo) in *. set (h2 := m_vmmaps mo2) in *.
    (* [comment removed for export] *)
    assert (NOTL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (a_L s) = false).
    { intros x Hx. destruct (in_rangesb x (a_L s)) eqn:E; [exfalso| reflexivity].
      pose proof (LM x E) as INM. rewrite (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) in INM; [discriminate|].
      unfold wz. rewrite !unsigned_lit by lia. exact Hx. }
    (* [comment removed for export] *)
    assert (SUBL : forall x : word, in_rangesb x L2 = true -> in_rangesb x (a_L s) = true).
    { intros x Hx. subst L2. unfold lg_L in Hx. destruct (nch =? nres); [| exact Hx]. rewrite in_rangesb_zcovb in Hx |- *.
      rewrite zcovb_maps_subtract in Hx by (first [exact NWL| lia]). apply andb_true_iff in Hx. exact (proj1 Hx). }
    assert (BANDL : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L2 = true).
    { intros x Hx. pose proof (ak_lsh s mo AK x Hx) as LX. rewrite SHLO in Hx. subst L2. unfold lg_L.
      destruct (nch =? nres); [| exact LX]. rewrite in_rangesb_zcovb in LX |- *. rewrite zcovb_maps_subtract by (first [exact NWL| lia]).
      rewrite LX. apply andb_true_iff. split; [reflexivity|]. apply negb_true_iff. apply zinb_false. lia. }
    (* [comment removed for export] *)
    assert (BANDL2 : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x L2 = true).
    { intros x Hx. pose proof (ak_lsl s mo AK x Hx) as LX. unfold sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in Hx. subst L2. unfold lg_L.
      destruct (nch =? nres); [| exact LX]. rewrite in_rangesb_zcovb in LX |- *. rewrite zcovb_maps_subtract by (first [exact NWL| lia]).
      rewrite LX. apply andb_true_iff. split; [reflexivity|]. apply negb_true_iff. apply zinb_false. lia. }
    (* [comment removed for export] *)
    assert (NASUB : forall x : word, in_rangesb x (vm_noaccess h) = false -> in_rangesb x (vm_noaccess h2) = false).
    { intros x Hx. rewrite VA2. rewrite in_rangesb_zcovb in Hx |- *.
      destruct (nch =? nres); [apply zcovb_maps_subtract_false; [exact NWA| lia| lia| exact Hx] | exact Hx]. }
    assert (NWA2 : entries_nowrap (vm_noaccess h2)).
    { rewrite VA2. destruct (nch =? nres); [apply maps_subtract_nowrap; [exact NWA| lia| lia] | exact NWA]. }
    assert (INCONS : forall (x : word) e, in_rangesb x (vm_maps h) = true -> in_rangesb x (e :: vm_maps h) = true)
      by (intros x e Hx; rewrite in_rangesb_cons, Hx; apply orb_true_r).
    split; [| (* [comment removed for export] *) intros x Hx; unfold h2 in VM2 |- *; rewrite VM2; apply INCONS; exact (DCOV x Hx)].
    split.
    { (* [comment removed for export] *)
      split.
      { (* [comment removed for export] *)
        unfold amaps_in_ledger. change (m_vmmaps mo2) with h2. change (a_st s2) with st2. change (a_L s2) with L2.
        change (as_maps st2) with (large_maps st a size). change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]).
        unfold large_maps. fold r needed msz nch nres. fold nch. fold nres.
        split.
        { intros mp Hin K1 K2 K3 K4. rewrite VM2. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - exfalso. destruct (nch =? nres); [| destruct Hin]. destruct Hin as [<-|[]]. exact (K3 eq_refl).
          - destruct Hin as [<-|Hin]; [split; [left; reflexivity| cbn [mp_base]; clear - B1 B2 B3; acb; lia]|].
            destruct (A1 mp Hin K1 K2 K3 K4) as [X Y]. exact (conj (or_intror X) Y). }   (* [comment removed for export] *)
        split.
        { intros mp Hin KK x Hx. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - (* [comment removed for export] *)
            destruct (Z.eqb_spec nch nres) as [EC|NE]; [| destruct Hin]. destruct Hin as [<-|[]]. cbn [mp_base mp_size] in Hx.
            assert (SL : pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 131072) by (change (as_ptr_array st) with pa in Hx; unfold kChunksBlockCount in Hx; fold nres in Hx; lia).
            split.
            + rewrite VA2. rewrite in_rangesb_zcovb. replace (nch =? nres) with true by (symmetry; apply Z.eqb_eq; exact EC).
              assert (N1 : zcovb (maps_subtract (vm_noaccess h) (pa + 8 * nres) (pa + 8 * nres + 131072)) (bv_unsigned x) = false).
              { rewrite zcovb_maps_subtract by (first [exact NWA| lia]). apply andb_false_iff. right. apply negb_false_iff. apply zinb_true. exact SL. }
              exact N1.
            + subst L2. unfold lg_L. replace (nch =? nres) with true by (symmetry; apply Z.eqb_eq; exact EC). rewrite in_rangesb_zcovb.
              assert (N1 : zcovb (maps_subtract (a_L s) (pa + 8 * nres) (pa + 8 * nres + 131072)) (bv_unsigned x) = false).
              { rewrite zcovb_maps_subtract by (first [exact NWL| lia]). apply andb_false_iff. right. apply negb_false_iff. apply zinb_true. exact SL. }
              exact N1.
          - destruct Hin as [<-|Hin]; [exfalso; destruct KK as [K|[[c [K|K]]|K]]; discriminate K|].
            destruct (A2 mp Hin KK x Hx) as [Q1 Q2]. split; [exact (NASUB x Q1)|].
            destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q2. discriminate Q2. }
        split.
        { intros sc x Hin Hx. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]].
          - pose proof (A3 sc x Hin Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q.
          - cbn [sc_map_beg sc_map_size] in Hx. pose proof (NOTL x Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q. }
        rewrite VM2. split; [| split; [| exact NWA2]].
        - apply nooverlap_cons_free; [exact (region_free_app_r _ _ _ _ FREE)| exact NOV].
        - apply entries_nowrap_cons'; [| exact NW]. unfold entry_nowrap, LazyLedger.hi, LazyLedger.lo. cbn [fst snd]. unfold wz. rewrite !unsigned_lit by lia. lia. }
      split.
      { (* [comment removed for export] *)
        destruct ASV as [V1 V2]. unfold ashadow_visible. change (a_st s2) with st2. change (a_S s2) with (Wsh :: a_S s).
        change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]).
        split.
        - intros c x Hc Hx. rewrite in_rangesb_cons. rewrite (V1 c x Hc); [apply orb_true_r|].
          change (RB s2 c) with (RB s c) in Hx. change (get_region st2 c) with (get_region st c) in Hx. exact Hx.
        - intros sc x Hin Hx. rewrite in_rangesb_cons. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]].
          + rewrite (V2 sc x Hin Hx). apply orb_true_r.
          + cbn [sc_map_beg sc_map_size] in Hx. apply orb_true_iff. left. subst Wsh. apply (zin_W (sh a) (msz / 8)); lia. }
      (* [comment removed for export] *)
      destruct AB as [AB0 AB1]. unfold ABUDGET. change (a_AL s2) with AL2. change (a_S s2) with (Wsh :: a_S s). change (m_vmmaps mo2) with h2. rewrite VL2.
      rewrite (aPhi_regions s s2) by reflexivity.   (* [comment removed for export] *)
      rewrite pages_total_cons. pose proof (cl_bounds Wsh) as CB. subst Wsh. cbn [fst snd] in CB. unfold wz in CB. rewrite (unsigned_lit (msz / 8)) in CB by (first [clear - SZ ARE GEO BND B8 ACEILB CB; lia | lia]).
      pose proof (pages_total_nonneg (a_S s)) as PT. unfold page_size in *.
      replace (msz / 8 / 4096) with (msz / 32768) in CB by (rewrite Z.div_div by lia; reflexivity).
      subst AL2. unfold lg_cost in *. split; [lia|]. clear - AB1 CB PT EAG2 ALLOW B3; try acb. unfold wz in *. subst h. destruct (nch =? nres); lia. }
    (* [comment removed for export] *)
    destruct AK as (K1 & (K2a & K2c) & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11).   (* [comment removed for export] *)
    unfold akernel. change (m_vmmaps mo2) with h2. change (a_thr s2) with (a_thr s). change (a_ctx s2) with (a_ctx s). change (a_sb s2) with (a_sb s).
    change (a_pa s2) with pa. change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L2.
    rewrite VR2, VL2, VM2.
    split; [exact K1|]. split; [exact (conj K2a (eq_trans (nonvm_same_atop _ _ NV) K2c))|].
    split; [intros x Hx; apply INCONS; exact (K3 x Hx)|].
    split; [intros xa xn c Hc H1 H2; apply map_contains_cons; change (RB s2 c) with (RB s c) in H1, H2; exact (K4a xa xn c Hc H1 H2)|].
    split; [intros xa xn H1 H2; apply map_contains_cons; exact (K4b xa xn H1 H2)|].
    split; [intros xa xn H1 H2 H3; apply map_contains_cons; exact (K4c xa xn H1 H2 H3)|].
    split; [exact K5a|]. split; [exact K5b|].
    split; [intros x Hx; split; [exact (proj1 (K5c x Hx))| exact (BANDL x Hx)]|].
    split.
    { (* [comment removed for export] *) intros x Hx. apply INCONS. apply K6a. destruct (in_rangesb x (vm_noaccess h)) eqn:E. { unfold h in E. first [exact E| reflexivity]. } rewrite (NASUB x E) in Hx. discriminate Hx. }
    split.
    { (* [comment removed for export] *)
      intros sc x Hin Hx. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
      assert (E0 : in_rangesb x (vm_noaccess h) = false).
      { destruct Hin as [Hin|[<-|[]]]; [exact (K6b sc x Hin Hx)|]. cbn [sc_map_beg sc_map_size] in Hx.
        destruct (in_rangesb x (vm_noaccess h)) eqn:E; [exfalso| reflexivity].
        pose proof (K6a x E) as INM. rewrite (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) in INM; [discriminate|].
        unfold wz. rewrite !unsigned_lit by lia. exact Hx. }
      destruct (in_rangesb x (vm_noaccess h2)) eqn:E2; [| reflexivity]. rewrite (NASUB x E0) in E2. discriminate E2. }
    split.
    { intros sc Hin. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
      destruct Hin as [Hin|[<-|[]]]; [right; exact (K7 sc Hin)| left; reflexivity]. }
    split; [intros x Hx; apply INCONS; exact (K8a x Hx)|].
    split; [intros xa xn H1 H2 H3; apply map_contains_cons; exact (K8b xa xn H1 H2 H3)|].
    split; [intros x Hx; split; [exact (proj1 (K8c x Hx))| exact (BANDL2 x Hx)]|].
    split; [exact K9|].
    split.
    2:{ (* [comment removed for export] *)
        intros xa xn HB. pose proof (K11 xa xn HB) as FR0. rewrite VA2.
        destruct (nch =? nres); [apply LazyMadvise.region_free_maps_subtract; [exact NWA| exact FR0]| exact FR0]. }
    { (* [comment removed for export] *)
      destruct K10 as (C1 & C2 & C3). change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]). unfold hsec in *.
      rewrite hcnt_cons, hlen_cons, zlen_filter_app, zsum_size_filter_app. rewrite (ehigh_wz a msz) by lia.
      assert (SH : forall z, schigh (mkSC a msz z) = (AHI_LO <? a + msz)) by (intros z; reflexivity). rewrite !SH.
      cbn [List.filter snd]. rewrite !SH. replace (bv_unsigned (wz msz)) with msz by (unfold wz; rewrite unsigned_lit by lia; reflexivity).
      split; [| split].
      - destruct (AHI_LO <? a + msz); unfold zlen in *; cbn [length map] in *; clear - C1; subst h st; change (Z.of_nat 1) with 1; change (Z.of_nat 0) with 0; lia.
      - destruct (AHI_LO <? a + msz); cbn [map SecGap.zsum sc_map_size] in *; clear - C2; subst h st; repeat match goal with x := _ |- _ => subst x end; lia.
      - intros sc Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]]; [exact (C3 sc Hin)|].
        cbn [sc_map_size]. unfold ASECMAX. pose proof GEO as (G1 & G2 & G3 & G4 & _). clear - G1 G2 G3 G4 SZ. subst msz needed r. lia. }
  Qed.
End ModelAfterLarge.

End HCW.

