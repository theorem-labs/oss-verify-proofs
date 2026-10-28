(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazyLedger AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require LazyMadvise.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX AsDepotInv AW_DepotFrame
     AllocWalkKit SecLazy SecLazy2 AS_SecRecycle1 AS_SecRecycle2 AG_Malloc AG_Malloc2 AG_MallocModel AG_WFHit AG_FreeModel AG_WFFree
     AG_RepQ AG_RepQFacts AG_RepQFacts2 AG_RepQFrame2 AG_RecycleModel AG_WriteSet AG_RecycleDefs AG_RecycleSecModel AG_RecycleSec1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma nooverlap_in_in : forall X e1 e2, nooverlap X -> In e1 X -> In e2 X ->
    e1 = e2 \/ LazyLedger.hi e1 <= LazyLedger.lo e2 \/ LazyLedger.hi e2 <= LazyLedger.lo e1.
  Proof.
    induction X as [|e X IH]; intros e1 e2 NO H1 H2; [destruct H1|]. destruct NO as [D NO].
    destruct H1 as [<-|H1], H2 as [<-|H2].
    - left; reflexivity.
    - right. exact (D e2 H2).
    - right. destruct (D e1 H1) as [L|L]; [right; exact L| left; exact L].
    - exact (IH e1 e2 NO H1 H2).
  Qed.
  Lemma zsum_perm : forall l l', Permutation l l' -> SecGap.zsum l = SecGap.zsum l'.
  Proof. intros l l' P. induction P; cbn in *; lia. Qed.
End HCW.

Section RSModel.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m0 : mem) (XC XB : list Z) (ch : chunk) (idx : nat) (h lsth : schunk) (d : depot) (lo : Z).
  Let st := a_st s.
  Let T := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let pa := a_pa s.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let mch := ch_chunk_beg ch.
  Let U := ch_user_beg ch.
  Let a := sc_map_beg h.
  Let msz := sc_map_size h.
  Let lst := sc_map_beg lsth.
  Let l1 := secdel_l1 (as_sec st) idx.
  Let st2 := remove_map (set_sec (del_state st ch) nres l1) a.
  Let L2 := rs_L (a_L s) a msz.
  Let s2 := mkAst st2 T CTX (a_fsb s) L2 (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).

  Hypothesis RQ : AREPQ s (mch :: XC) XB m0.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis SEC : ch_primary ch = false.
  Hypothesis QUAR : ch_state ch = CQuarantine.
  Hypothesis HIDX : nth_error (as_sec st) idx = Some h.
  Hypothesis HMAP : sc_map_beg h = sec_map_beg ch.
  Hypothesis HLAST : nth_error (as_sec st) (length (as_sec st) - 1)%nat = Some lsth.
  Hypothesis DPL : depot_placed s d.
  Hypothesis LO : aceil <= lo.

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let HIN : In h (as_sec st). Proof. eapply nth_error_In. exact HIDX. Qed.
  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SECP & SEC2 & TCX).


  Let BND : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 12599296 <= pa /\ pa + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 12599296 <= a /\ a + msz <= aceil /\ 8192 <= msz /\ 2148314624 <= sh a /\ sh a + msz / 8 <= sh aceil
            /\ 1 <= nch <= nres /\ nres <= 16384 /\ 12599296 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil
            /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ (idx < length (as_sec st))%nat /\ 12599296 <= lst /\ lst + 8192 <= aceil /\ lst mod 4096 = 0.
  Proof. eapply rs_bnd; eassumption. Qed.
  Let BANDS : hidden ((T + 4096 <= 65536 \/ (12599296 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 131072 <= 2147446784 \/ 17594333495296 <= d_sb d)
                   /\ (a + msz <= 2147446784 \/ 17594333495296 <= a)
                   /\ (sh a + msz / 8 <= 2415881728 \/ 2201439137792 <= sh a)
                   /\ (a_fsb s + AFS_SIZE <= 2147446784 \/ 17594333495296 <= a_fsb s)
                   /\ (lst + 8192 <= 2147446784 \/ 17594333495296 <= lst)).
  Proof. eapply rs_bands; eassumption. Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).
  Let PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz T kPageSize /\ disj a msz CTX 160
            /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 131072)
            /\ (forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> disj a msz (sc_map_beg sc) (sc_map_size sc)).
  Proof. eapply rs_pnew; eassumption. Qed.
  Let L1IN : forall y, In y l1 <-> In y (as_sec st) /\ sc_map_beg y <> a.
  Proof. eapply rs_l1in; eassumption. Qed.
  Let SUB1 : forall y, In y l1 -> In y (as_sec st). Proof. intros y Hy. exact (proj1 (proj1 (L1IN y) Hy)). Qed.


  Section Model.
    Variables (mo mo2 : Model).
    Hypothesis AMX : AMODELX s mo.
    Hypothesis DCOV : depot_cov d mo.
    Hypothesis MO : rs_model mo a msz mo2.
    Hypothesis NWL : entries_nowrap (a_L s).          (* [comment removed for export] *)
    Let hh := m_vmmaps mo.
    Let h2 := m_vmmaps mo2.
    Let L1 := a_L s.   (* [comment removed for export] *)

    Theorem amodelx_after_rs : AMODELX s2 mo2 /\ depot_cov d mo2.
    Proof.
      destruct AMX as [AM AK]. destruct AM as (AIL & ASV & AB). destruct AIL as (A1 & A2 & A3 & NOV & NW & NWA).
      pose proof MO as M; unfold rs_model in M; cbv beta iota zeta in M. destruct M as (NV & VM2 & VR2 & VL2 & VB2 & VK2 & VS2 & VA2 & EAG2).
      fold hh h2 in VM2, VR2, VL2, VB2, VK2, VS2, VA2.
      pose proof BND as B. bands_as (BT & _ & BP & _ & _ & BA & BS & BF & _).
      pose proof AK as AK'. destruct AK' as (K1 & (K2a & K2c) & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11). fold hh in K1, K2a, K2c, K3, K4a, K4b, K4c, K6a, K6b, K7, K8a, K8b, K9, K10, K11.
      assert (SHLO : sh AHI_LO = 0x2008fff7000) by (rewrite <- AHSB_eq; reflexivity). pose proof sh_ceiling_range as SCV.
      assert (WA : bv_unsigned (wz a) = a) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      assert (WM : bv_unsigned (wz msz) = msz) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      (* [comment removed for export] *)
      assert (SHB : (sh AHI_LO <= sh a /\ sh a + msz / 8 <= sh aceil) \/ (sh AIMG_TOP <= sh a /\ sh a + msz / 8 <= sh ALOWSH_LO)).
      { destruct BA as [X|X]; [right| left]; unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO in *; clear - X B; try acb; Z.div_mod_to_equations; lia. }
      assert (E0IN : In (wz a, wz msz) (vm_maps hh)) by exact (K7 h HIN).
      (* [comment removed for export] *)
      assert (BASED : forall r, In r (vm_maps hh) -> bv_unsigned (fst r) = a -> r = (wz a, wz msz) \/ bv_unsigned (snd r) = 0).
      { intros r Hr Hb. pose proof (bv_unsigned_in_range _ (snd r)) as RR.
        destruct (nooverlap_in_in _ _ _ NOV Hr E0IN) as [E|[D|D]]; [left; exact E| right| right];
          unfold LazyLedger.lo, LazyLedger.hi in D; cbn [fst snd] in D; rewrite ?WA, ?WM in D; clear - D Hb B RR; try acb; lia. }
      (* [comment removed for export] *)
      assert (RM : forall r, In r (vm_maps hh) -> bv_unsigned (fst r) <> a -> In r (vm_maps h2)).
      { intros r Hr NE. unfold h2 in VM2 |- *. rewrite VM2. unfold map_remove. apply filter_In. split; [exact Hr|]. rewrite bv_eqb_Z, WA. apply negb_true_iff. apply Z.eqb_neq. exact NE. }
      assert (KEEP : forall x : word, in_rangesb x (vm_maps hh) = true -> ~ (a <= bv_unsigned x < a + msz) -> in_rangesb x (vm_maps h2) = true).
      { intros x Hx NI. rewrite in_rangesb_zcovb in Hx |- *. apply zcovb_true in Hx as (r & Hr & R). apply zcovb_true. exists r. split; [| exact R].
        apply RM; [exact Hr|]. intros Eb. destruct (BASED r Hr Eb) as [->|Z0].
        - unfold LazyLedger.lo, LazyLedger.hi in R. cbn [fst snd] in R. rewrite WA, WM in R. exact (NI R).
        - unfold LazyLedger.lo, LazyLedger.hi in R. rewrite Eb, Z0 in R. clear - R. lia. }
      assert (MC0 : forall xa xn y : word, bv_unsigned xn = 0 -> in_rangesb y (vm_maps h2) = true ->
                (bv_unsigned y = bv_unsigned xa \/ bv_unsigned y + 1 = bv_unsigned xa) -> map_contains (vm_maps h2) xa xn = true).
      { intros xa xn y Z0 Hy EY. rewrite in_rangesb_zcovb in Hy. apply zcovb_true in Hy as (r & Hr & R). unfold LazyLedger.lo, LazyLedger.hi in R.
        unfold map_contains. apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; apply Z.leb_le; clear - R EY Z0; lia. }
      assert (MCKEEP : forall xa xn : word, map_contains (vm_maps hh) xa xn = true -> 0 < bv_unsigned xn ->
                (bv_unsigned xa + bv_unsigned xn <= a \/ a + msz <= bv_unsigned xa) -> map_contains (vm_maps h2) xa xn = true).
      { intros xa xn MC POS D. apply LazyNodes.map_contains_In in MC as (r & Hr & R1 & R2). unfold LazyLedger.lo, LazyLedger.hi in R1, R2.
        unfold map_contains. apply existsb_exists. exists r. split.
        - apply RM; [exact Hr|]. intros Eb. destruct (BASED r Hr Eb) as [->|Z0].
          + cbn [fst snd] in R1, R2. rewrite WA in R1. rewrite WA, WM in R2. clear - R1 R2 POS D B; try acb. lia.
          + rewrite Z0 in R2. clear - R1 R2 POS Eb. lia.
        - apply andb_true_iff. split; apply Z.leb_le; lia. }
      (* [comment removed for export] *)
      assert (NWL1 : entries_nowrap L1) by exact NWL.
      assert (SUBL1 : forall x : word, in_rangesb x L1 = true -> in_rangesb x (a_L s) = true) by (intros x Hx; exact Hx).
      assert (SUBL : forall x : word, in_rangesb x L2 = true -> in_rangesb x (a_L s) = true).
      { intros x Hx. apply SUBL1. subst L2. unfold rs_L in Hx. fold L1 in Hx. rewrite in_rangesb_zcovb in Hx |- *.
        rewrite zcovb_maps_subtract in Hx; [apply andb_true_iff in Hx; exact (proj1 Hx)| exact NWL1| |]; clear - B; try acb; lia. }
      assert (INL2 : forall x : word, in_rangesb x (a_L s) = true -> ~ (a <= bv_unsigned x < a + msz) -> in_rangesb x L2 = true).
      { intros x Hx N1. subst L2. unfold rs_L. fold L1. rewrite in_rangesb_zcovb in Hx |- *.
        rewrite zcovb_maps_subtract; [| exact NWL1| clear - B; try acb; lia| clear - B; try acb; lia]. apply andb_true_iff. split; [| apply negb_true_iff; apply zinb_false; exact N1].
        exact Hx. }
      assert (BANDL : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L2 = true).
      { intros x Hx. apply INL2; [exact (ak_lsh s mo AK x Hx)|]. clear - Hx BA B SHLO SCV; try acb. lia. }
      assert (BANDL2 : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x L2 = true).
      { intros x Hx. apply INL2; [exact (ak_lsl s mo AK x Hx)|]. unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO in Hx. clear - Hx BA B; try acb. lia. }
      (* [comment removed for export] *)
      assert (NWA1 : entries_nowrap (vm_noaccess hh)) by exact NWA.
      assert (NASUP : forall x : word, in_rangesb x (vm_noaccess h2) = true -> in_rangesb x (vm_noaccess hh) = true /\ ~ (a <= bv_unsigned x < a + msz)).
      { intros x Hx. rewrite VA2 in Hx. rewrite in_rangesb_zcovb in Hx |- *.
        rewrite zcovb_maps_subtract in Hx; [| exact NWA1| clear - B; try acb; lia| clear - B; try acb; lia]. apply andb_true_iff in Hx. destruct Hx as [Hx Hn].
        apply negb_true_iff in Hn. apply zinb_false in Hn. split; [| exact Hn]. exact Hx. }
      assert (NASUB : forall x : word, in_rangesb x (vm_noaccess hh) = false -> in_rangesb x (vm_noaccess h2) = false).
      { intros x Hx. destruct (in_rangesb x (vm_noaccess h2)) eqn:E; [| reflexivity]. rewrite (proj1 (NASUP x E)) in Hx. discriminate Hx. }
      assert (NWA2 : entries_nowrap (vm_noaccess h2)).
      { rewrite VA2. apply maps_subtract_nowrap; [exact NWA1| |]; clear - B; try acb; lia. }
      split.
      2:{ (* [comment removed for export] *)
        intros x Hx. apply KEEP; [exact (DCOV x Hx)|]. destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & G9 & _). destruct (G9 h HIN) as [E1 E2].
        fold a msz in E1, E2. unfold disj in E1, E2. clear - Hx E1 E2. lia. }
      split.
      { (* [comment removed for export] *)
        split.
        { (* [comment removed for export] *)
          unfold amaps_in_ledger. change (m_vmmaps mo2) with h2. change (a_st s2) with st2. change (a_L s2) with L2.
          change (as_maps st2) with (List.filter (fun mp => negb (mp_base mp =? a)) (as_maps st)). change (as_sec st2) with l1.
          split.
          { intros mp Hin K1' K2' K3' K4'. apply filter_In in Hin. destruct Hin as [Hin NB]. apply negb_true_iff in NB. apply Z.eqb_neq in NB.
            destruct (A1 mp Hin K1' K2' K3' K4') as [INV RANGE].      (* [comment removed for export] *)
            split; [| exact RANGE]. apply RM; [exact INV|]. cbn [fst]. rewrite unsigned_lit by exact RANGE. exact NB. }
          split.
          { intros mp Hin KK x Hx. apply filter_In in Hin. destruct Hin as [Hin _]. destruct (A2 mp Hin KK x Hx) as [Q1 Q2]. split; [exact (NASUB x Q1)|].
            destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q2. discriminate Q2. }
          split.
          { intros sc x Hin Hx. pose proof (A3 sc x (SUB1 sc Hin) Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q. }
          unfold h2 in VM2 |- *. rewrite VM2. split; [apply nooverlap_map_remove; exact NOV|]. split; [apply entries_nowrap_map_remove; exact NW| exact NWA2]. }
        split.
        { (* [comment removed for export] *)
          destruct ASV as [V1 V2]. unfold ashadow_visible. change (a_st s2) with st2. change (a_S s2) with (a_S s). change (as_sec st2) with l1.
          split; [intros c x Hc Hx; apply (V1 c x Hc); exact Hx| intros sc x Hin Hx; exact (V2 sc x (SUB1 sc Hin) Hx)]. }
        (* [comment removed for export] *)
        destruct AB as [AB0 AB1]. unfold ABUDGET. change (a_AL s2) with (a_AL s). change (a_S s2) with (a_S s). change (m_vmmaps mo2) with h2. rewrite VL2.
        rewrite (aPhi_regions s s2) by reflexivity. split; [exact AB0|]. fold hh in AB1. clear - AB1 EAG2 B; try acb. lia. }
      (* [comment removed for export] *)
      unfold akernel. change (m_vmmaps mo2) with h2. change (a_thr s2) with T. change (a_ctx s2) with CTX. change (a_sb s2) with sb.
      change (a_pa s2) with pa. change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L2. change (a_st s2) with st2. change (as_sec st2) with l1.
      fold T CTX sb pa in K3, K4b, K5a, K5b. destruct PNEW as (N1 & N2 & N3 & N4 & N5 & _). unfold disj in N1, N2, N3, N4, N5.
      rewrite VR2, VL2.
      split; [exact K1|]. split; [exact (conj K2a (eq_trans (nonvm_same_atop _ _ NV) K2c))|].
      split.
      { intros x Hx. apply KEEP; [exact (K3 x Hx)|]. unfold kPageSize, kSpaceSize, kPtrArrayReserve, AFS_SIZE, AHI_LO in *.
        destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]; [clear - Hx N3| clear - Hx N4| clear - Hx N1| clear - Hx N2| clear - Hx N5| clear - Hx BA B SHLO; try acb]; lia. }
      split.
      { intros xa xn c Hc H1 H2. change (RB s2 c) with (RB s c) in H1, H2.
        assert (SP : sb <= RB s c /\ RB s c + kRegionSize <= sb + kSpaceSize).
        { unfold RB, sb, a_sb. rewrite region_beg_eq. unfold kRegionSize, kSpaceSize, kNumClasses in *. clear - Hc. lia. }
        destruct (Z.eq_dec (bv_unsigned xn) 0) as [Z0|NZ].
        - apply (MC0 xa xn xa); [exact Z0| | left; reflexivity]. apply KEEP; [apply K3; do 2 right; left| ]; unfold kRegionSize, kSpaceSize, kPageSize in *; clear - H1 H2 Z0 SP N1; lia.
        - apply MCKEEP; [exact (K4a xa xn c Hc H1 H2)| pose proof (bv_unsigned_in_range _ xn); clear - NZ H; lia|].
          unfold kRegionSize, kSpaceSize, kPageSize in *; clear - H1 H2 SP N1; lia. }
      split.
      { intros xa xn H1 H2. destruct (Z.eq_dec (bv_unsigned xn) 0) as [Z0|NZ].
        - (* [comment removed for export] *)
          destruct (Z.lt_ge_cases (bv_unsigned xa) (pa + kPtrArrayReserve)) as [XL|XG].
          + apply (MC0 xa xn xa); [exact Z0| | left; reflexivity]. apply KEEP; [apply K3; do 3 right; left| ]; unfold kPtrArrayReserve in *; clear - H1 XL N2; lia.
          + pose proof (bv_unsigned_in_range _ xa) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
            assert (WY : bv_unsigned (wz (bv_unsigned xa - 1)) = bv_unsigned xa - 1) by (unfold wz; apply unsigned_lit; clear - H1 XR B; try acb; lia).
            apply (MC0 xa xn (wz (bv_unsigned xa - 1))); [exact Z0| | rewrite WY; right; lia].
            apply KEEP; [apply K3; do 3 right; left| ]; rewrite WY; unfold kPtrArrayReserve in *; clear - H1 H2 Z0 XG N2 B; try acb; lia.
        - apply MCKEEP; [exact (K4b xa xn H1 H2)| pose proof (bv_unsigned_in_range _ xn); clear - NZ H; lia|]. unfold kPtrArrayReserve in *; clear - H1 H2 N2; lia. }
      split.
      { intros xa xn H1 H2 H3. apply MCKEEP; [exact (K4c xa xn H1 H2 H3)| exact H2|]. clear - H1 H3 BA B SHLO SCV; try acb. unfold AHI_LO in *. lia. }
      split; [exact K5a|]. split; [exact K5b|].
      split; [intros x Hx; split; [exact (proj1 (K5c x Hx))| exact (BANDL x Hx)]|].
      split.
      { (* [comment removed for export] *) intros x Hx. destruct (NASUP x Hx) as [Hx' NI]. exact (KEEP x (K6a x Hx') NI). }
      split.
      { (* [comment removed for export] *) intros sc x Hin Hx. apply NASUB. exact (K6b sc x (SUB1 sc Hin) Hx). }
      split.
      { (* [comment removed for export] *)
        intros sc Hin. pose proof (proj1 (L1IN sc) Hin) as [Hin0 NE]. apply RM; [exact (K7 sc Hin0)|]. cbn [fst].
        placed. pose proof (SECP sc Hin0) as (_ & Q2 & Q3 & Q4 & _). apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
        unfold wz. rewrite unsigned_lit by (clear - Q2 Q3 Q4; try acb; unfold kPageSize in *; lia). exact NE. }
      split.
      { intros x Hx. apply KEEP; [exact (K8a x Hx)|]. unfold ALOWSH_LO, AHI_LO in Hx. clear - Hx BA B; try acb. lia. }
      split.
      { intros xa xn H1 H2 H3. apply MCKEEP; [exact (K8b xa xn H1 H2 H3)| exact H2|]. unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO in H1, H3. clear - H1 H3 BA B; try acb. lia. }
      split; [intros x Hx; split; [exact (proj1 (K8c x Hx))| exact (BANDL2 x Hx)]|].
      split; [exact K9|].
      split.
      2:{ (* [comment removed for export] *)
          intros xa xn HB. rewrite VA2. apply LazyMadvise.region_free_maps_subtract; [exact NWA| exact (K11 xa xn HB)]. }
      (* [comment removed for export] *)
      destruct K10 as (C1 & C2 & C3). unfold hsec in *. change (as_sec st2) with l1. change (as_sec (a_st s)) with (as_sec st) in C1, C2, C3.
      pose proof (Permutation_filter schigh _ _ (secdel_l1_perm _ _ _ HIDX)) as PF. fold l1 in PF. cbn [List.filter] in PF.
      assert (EHI : KInv.ehi (wz a, wz msz) = a + msz) by (unfold KInv.ehi; cbn [fst snd]; rewrite WA, WM; reflexivity).
      unfold h2 in VM2 |- *. rewrite VM2.
      destruct (schigh h) eqn:SH; rewrite ?SH in PF; cbv iota in PF;
        pose proof (Permutation_length PF) as PL0; pose proof (zsum_perm _ _ (Permutation_map sc_map_size PF)) as PS;
        cbn [length] in PL0; cbn [map SecGap.zsum] in PS; fold msz in PS; unfold zlen in *; rewrite <- PL0 in C1; rewrite <- PS in C2.
      - (* [comment removed for export] *)
        unfold schigh in SH. apply Z.ltb_lt in SH. fold a msz in SH. rewrite <- EHI in SH.
        pose proof (hcnt_map_remove_in _ _ E0IN SH) as HC. pose proof (hlen_map_remove_in _ _ E0IN SH) as HL. cbn [fst snd] in HC, HL. rewrite WM in HL.
        split; [clear - HC C1; lia|]. split; [clear - HL C2; lia|]. intros sc Hin. exact (C3 sc (SUB1 sc Hin)).
      - pose proof (hcnt_map_remove_le (vm_maps hh) (wz a)) as HC. pose proof (hlen_map_remove_le (vm_maps hh) (wz a)) as HL.
        split; [clear - HC C1; lia|]. split; [clear - HL C2; lia|]. intros sc Hin. exact (C3 sc (SUB1 sc Hin)).
    Qed.

    (* [comment removed for export] *)
    Lemma keep_rs : forall x : word, in_rangesb x (vm_maps hh) = true -> ~ (a <= bv_unsigned x < a + msz) -> in_rangesb x (vm_maps h2) = true.
    Proof.
      destruct AMX as [AM AK]. destruct AM as (AIL & _ & _). destruct AIL as (_ & _ & _ & NOV & _ & _).
      pose proof MO as M; unfold rs_model in M; cbv beta iota zeta in M. destruct M as (_ & VM2 & _). fold hh h2 in VM2.
      pose proof BND as B.
      assert (WA : bv_unsigned (wz a) = a) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      assert (WM : bv_unsigned (wz msz) = msz) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      assert (E0IN : In (wz a, wz msz) (vm_maps hh)) by exact (ak_secmaps s mo AK h HIN).
      intros x Hx NI. rewrite in_rangesb_zcovb in Hx |- *. apply zcovb_true in Hx as (r & Hr & R). apply zcovb_true. exists r. split; [| exact R].
      unfold h2 in VM2 |- *. rewrite VM2. unfold map_remove. apply filter_In. split; [exact Hr|]. rewrite bv_eqb_Z, WA. apply negb_true_iff. apply Z.eqb_neq.
      intros Eb. pose proof (bv_unsigned_in_range _ (snd r)) as RR.
      unfold LazyLedger.lo, LazyLedger.hi in R.
      destruct (nooverlap_in_in _ _ _ NOV Hr E0IN) as [E|[D|D]].
      - subst r. cbn [fst snd] in R. rewrite WA, WM in R. exact (NI R).
      - unfold LazyLedger.lo, LazyLedger.hi in D; cbn [fst snd] in D; rewrite ?WA, ?WM in D. clear - D Eb R B RR; try acb; lia.
      - unfold LazyLedger.lo, LazyLedger.hi in D; cbn [fst snd] in D; rewrite ?WA, ?WM in D. clear - D Eb R B RR; try acb; lia.
    Qed.
    Lemma avmx_after_rs : avmx s s2 mo mo2.
    Proof.
      intros x Hx. split.
      - destruct (Z.lt_ge_cases (bv_unsigned x) a) as [LT|GE]; [left; apply keep_rs; [exact Hx| clear - LT; lia]|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (a + msz)) as [LT2|GE2]; [| left; apply keep_rs; [exact Hx| clear - GE2; lia]].
        right. exists h. split; [exact HIN|]. split; [| exact (conj GE LT2)].
        intros Hin. change (as_sec (a_st s2)) with l1 in Hin. exact (proj2 (proj1 (L1IN h) Hin) eq_refl).
      - intros sc Hin NIn. exfalso. apply NIn. change (as_sec (a_st s2)) with l1 in Hin. exact (SUB1 sc Hin).
    Qed.
  End Model.
End RSModel.
