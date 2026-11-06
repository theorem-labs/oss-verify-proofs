(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_dll MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_free MallocInv_tryavail MallocInv_ameta_iface
  MallocInv_ntfree MallocInv_ntpieces MallocInv_ntpost MallocInv_ntq MallocInv_ntok
  MallocInv_ntd MallocInv_ntk MallocInv_ntg MallocInv_ntn.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Lemma mask_all_idle : forall A ma mt aib slots i, WF A -> a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  nth_error slots (Z.to_nat i) = Some STaken -> 0 <= i ->
  Z.lor (mt_avail mt) (mt_freed mt) + 2^i = 2^(mt_cnt mt) - 1 ->
  forall j st, nth_error slots j = Some st -> st = SIdle \/ st = STaken.
Proof.
  intros A ma mt aib slots i HW Hma Hr Hi Hi0 Hall j st Hj.
  destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & Hlen & Hav & Hfd & Hdis & _ & _ & _ & Hidle & _).
  set (mask := Z.lor (mt_avail mt) (mt_freed mt)) in *.
  assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
  assert (Hjlt : (j < length slots)%nat) by (apply (proj1 (nth_error_Some slots j)); rewrite Hj; discriminate).
  assert (Hm : 0 <= mask < 2^(mt_cnt mt)) by (unfold mask; apply lor_range; lia).
  destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne]; [rewrite Hi in Hj; injection Hj as <-; right; reflexivity|].
  left. apply (proj1 (Hidle (Z.of_nat j) st ltac:(rewrite Nat2Z.id; exact Hj) ltac:(lia))).
  assert (Hbi : Z.testbit mask i = false).
  { destruct (Z.testbit mask i) eqn:E; [| reflexivity]. exfalso.
    pose proof (proj1 (Hidle i STaken Hi Hi0) E). discriminate. }
  destruct (add_clear_bit mask i (mt_cnt mt) Hm ltac:(lia) Hbi) as [E _].
  assert (Ht : Z.testbit (Z.lor mask (2^i)) (Z.of_nat j) = true).
  { rewrite <- E. fold mask in Hall. rewrite Hall. replace (2 ^ mt_cnt mt - 1) with (Z.ones (mt_cnt mt)) by (rewrite Z.ones_equiv; lia).
    apply Z.ones_spec_low. lia. }
  rewrite Z.lor_spec, Z.pow2_bits_eqb in Ht by lia.
  replace (i =? Z.of_nat j) with false in Ht by (symmetry; apply Z.eqb_neq; lia).
  rewrite Bool.orb_false_r in Ht. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma next0_notact : forall A ma mt aib slots, WF A -> ACT48 A -> a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  mt_next mt = 0 -> forall c, ~ In ma (a_active A c).
Proof.
  intros A ma mt aib slots HW H48 Hma Hr Hn c Hin.
  assert (Hc : 0 <= c < 48).
  { destruct (Z.lt_ge_cases c 0) as [H | H]; [rewrite (H48 c) in Hin by lia; destruct Hin|].
    destruct (Z.lt_ge_cases c 48) as [H' | H']; [lia|]. rewrite (H48 c) in Hin by lia. destruct Hin. }
  destruct (In_nth_error _ _ Hin) as [k Hk].
  destruct (wf_act_dll A HW c Hc k ma Hk) as (mt' & Hm' & Hnx & _). rewrite Hma in Hm'. injection Hm' as <-.
  assert (Hlen : (0 < length (a_active A c))%nat) by (destruct (a_active A c); [destruct Hin | cbn; lia]).
  pose proof (nth_In (a_active A c) 0 (Nat.mod_upper_bound (S k) (length (a_active A c)) ltac:(lia))) as Hin2.
  rewrite <- Hnx in Hin2.
  destruct (wf_act_mem A HW c _ Hin2) as (mt2 & aib2 & sl2 & Hm2 & _).
  pose proof (meta_facts A _ mt2 HW Hm2) as (X1 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma nfuel_w32 : forall mt mt', mt_w32 mt' = mt_w32 mt -> nfuel mt' = nfuel mt.
Proof.
  intros mt mt' Hw. unfold nfuel, glvl, gextent, mt_stride, mt_cnt, mt_maplen, mt_last, mt_sc. rewrite Hw. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FreeGrp.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some STaken.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hall : Z.lor (mt_avail mt) (mt_freed mt) + 2^i = 2^(mt_cnt mt) - 1.
  Hypothesis H48 : ACT48 A.
  (* [comment removed for export] *)
  Variable rec : word -> word -> M (word * word).
  Hypothesis Hrec : forall D' A' s' pa pm paib psl j,
    II sp0 argv envp cb D' A' s' -> ACT48 A' -> a_meta A' pa = Some pm -> mt_role pm = RGroup paib psl ->
    nth_error psl (Z.to_nat j) = Some STaken -> 0 <= j -> (nfuel pm < nfuel mt)%nat ->
    tsafe (rec (Z_to_bv 64 pa) (Z_to_bv 64 j) s') (ntpost sp0 argv envp cb D' A' s' pa psl j).

  Theorem ts_nt_freegrp : forall (K : word * word -> M R) P,
    (forall s' A' r, II sp0 argv envp cb D A' s' -> ntframe A s s' -> ntrel A A' ma slots i -> nt_res A A' (ms_vm s) r ->
       (forall mtx aibx slx, a_meta A' ma = Some mtx -> mt_role mtx <> RGroup aibx slx) ->
       tsafe (K r s') P) ->
    tsafe ((r <- nt_freegrp rec (Z_to_bv 64 ma) (Z_to_bv 64 (mt_w32 mt)) (Z_to_bv 64 (mt_sc mt)) ;; K r) s) P.
  Proof.
    intros K P HK. pose proof (is_wf _ _ _ _ _ _ (ii_is HII)) as HW. pose proof (is_rep _ _ _ _ _ _ (ii_is HII)) as HR. pose proof (is_win _ _ _ _ _ _ (ii_is HII)) as HWIN.
    pose proof (mask_all_idle A ma mt aib slots i HW Hma Hr Hi Hi0 Hall) as Hidle.
    pose proof (grp_next_range A ma mt aib slots HW Hma Hr) as (Hnx & Hpv & Hmem).
    unfold nt_freegrp. reassoc. rewrite at_Z. change (ma + 8) with (ma + moff FNext).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | exact Hnx |].
    change (mt_f mt FNext) with (mt_next mt). reassoc.
    (* [comment removed for export] *)
    assert (TAIL : forall s1 A1, II sp0 argv envp cb D A1 s1 -> ntframe A s s1 -> deqrel A A1 ma mt ->
              tsafe ((r <- nt_fg rec (Z_to_bv 64 ma) ;; K r) s1) P).
    { intros s1 A1 HII1 HF1 HD1.
      destruct (dq_ma _ _ _ _ HD1) as (mt1 & Hma1 & Hr1 & Hw1 & Hm1 & Hav1 & Hfr1). rewrite Hr in Hr1.
      assert (H48' : ACT48 A1) by (intros c Hc; rewrite (dq_act _ _ _ _ HD1 c Hc); exact (H48 c Hc)).
      assert (Hml1 : mt_maplen mt1 = mt_maplen mt) by (unfold mt_maplen; rewrite Hw1; reflexivity).
      pose proof (dq_unlinked _ _ _ _ HD1) as Hun1.
      assert (POST : forall s' A' r, II sp0 argv envp cb D A' s' -> ntframe A1 s1 s' -> fgrel A1 A' ma -> nt_res A1 A' (ms_vm s1) r ->
                tsafe (K r s') P).
      { intros s' A' r HII' HF' HG' HRes'.
        destruct HD1 as [L1 Ar1 P1 B1 X1 F1 C1 Q1 M1 U1 G1 D1]. destruct HG' as [L2 Ar2 P2 B2 C2 Q2 G2 D2 FL2].
        apply (HK s' A' r HII').
        - apply (ntframe_trans A A1 s s1 s' HF1 HF'); [| exact L1].
          intros x [Hx | Hx]; [left; exact Hx | right; apply (proj1 (D1 x)); exact Hx].
        - constructor.
          + rewrite L2. exact L1. + rewrite Ar2. exact Ar1. + rewrite P2. exact P1. + rewrite B2. exact B1.
          + intros k Hk. rewrite (C2 k Hk). apply C1. intros c ->. exact Hk.
          + intros c Hc. rewrite (Q2 c Hc). exact (Q1 c Hc).
          + intros x mtx aibx slx Hx Hrx. destruct (G2 x mtx aibx slx Hx Hrx) as (Hne & mt2 & sl2 & Hx2 & Hr2 & W2 & Mm2 & K2).
            destruct (G1 x mt2 aibx sl2 Hx2 Hr2) as (mt0 & Hx0 & Hr0 & W0 & M0).
            exists mt0, sl2. split; [exact Hx0|]. split; [exact Hr0|]. split; [rewrite W0; exact W2|]. split; [rewrite M0; exact Mm2|].
            right. split; [exact Hne | exact K2].
          + intros x Hx. apply (proj1 (D1 x)). exact (D2 x Hx).
          + destruct FL2 as [l2 E2]. exists l2. rewrite E2, F1. reflexivity.
        - pose proof (nf_vm _ _ _ HF1) as V1.
          destruct HRes' as [(-> & HX & HD) | (B & L & -> & HL & HBal & HLm & Hhr & HX & Hin & Diff & Nod & Hav & WFx & VMx)].
          + left. split; [reflexivity|]. split; [rewrite HX; exact X1|]. intros x Hx. apply HD. apply (proj2 (D1 x)). exact Hx.
          + right. exists B, L. rewrite <- X1, <- V1. split; [reflexivity|]. split; [exact HL|]. split; [exact HBal|]. split; [exact HLm|]. split; [exact Hhr|].
            split; [exact HX|]. split; [exact Hin|]. split; [| split; [exact Nod | split; [exact Hav | split; [exact WFx | exact VMx]]]].
            intros x. rewrite <- (Diff x). symmetry. exact (D1 x).
        - intros mtx aibx slx Hx Hrx. exact (proj1 (G2 ma mtx aibx slx Hx Hrx) eq_refl). }
      pose proof (maplen_nonneg mt (proj1 (proj1 (wf_grp A HW ma mt aib slots Hma Hr)))) as Hmln.
      destruct (Z.eq_dec (mt_maplen mt) 0) as [Hml0 | Hmlp].
      - apply (ts_nt_fg_nested sp0 argv envp cb D A1 s1 HII1 ma mt1 aib slots Hma1 Hr1 Hidle Hun1 ltac:(lia) H48' rec); [| exact POST].
        intros D' A' s' pa pm paib psl j HII' H48'' Hpa Hpr Hj Hj0 Hf. rewrite (nfuel_w32 mt mt1 Hw1) in Hf.
        exact (Hrec D' A' s' pa pm paib psl j HII' H48'' Hpa Hpr Hj Hj0 Hf).
      - apply (ts_nt_fg_root sp0 argv envp cb D A1 s1 HII1 ma mt1 aib slots Hma1 Hr1 Hidle Hun1 ltac:(lia) rec).
        intros s' A' HII' HF' HG' HRes'. exact (POST s' A' _ HII' HF' HG' HRes'). }
    rewrite is0_Z by lia.
    destruct (Z.eqb_spec (mt_next mt) 0) as [Hn0 | Hn1].
    - apply ts_bind_ret. apply (TAIL s A HII (ntframe_refl A s)). apply (deqrel_refl A ma mt Hma).
      exact (next0_notact A ma mt aib slots HW H48 Hma Hr Hn0).
    - destruct (Hmem Hn1) as [Hin Hsc48]. destruct (in_split _ _ Hin) as (l1 & l2 & El).
      pose proof (w_sc_range (mt_w32 mt)) as Hscr.
      apply (ts_nt_deqact sp0 argv envp cb D A s HII ma mt Hma l1 l2 ltac:(unfold mt_sc in *; lia) El).
      intros s1 A1 HII1 HF1 HD1. exact (TAIL s1 A1 HII1 HF1 HD1).
  Qed.
End FreeGrp.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte).

  Lemma nfuel_pos : forall A ma mt aib slots, WF A -> a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> (1 <= nfuel mt)%nat.
  Proof.
    intros A ma mt aib slots HW Hma Hr. unfold nfuel. destruct (0 <? mt_maplen mt) eqn:E; [lia|].
    apply Z.ltb_ge in E. pose proof (maplen_nonneg mt (proj1 (proj1 (wf_grp A HW ma mt aib slots Hma Hr)))) as Hmln.
    pose proof (glvl_range A HW ma mt aib slots Hma Hr ltac:(lia)). lia.
  Qed.

  Theorem ntfree_ok : forall fuel D A s ma mt aib slots i,
    II sp0 argv envp cb D A s -> ACT48 A -> a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    nth_error slots (Z.to_nat i) = Some STaken -> 0 <= i -> (nfuel mt <= fuel)%nat ->
    tsafe (m_nontrivial_free fuel (Z_to_bv 64 ma) (Z_to_bv 64 i) s) (ntpost sp0 argv envp cb D A s ma slots i).
  Proof.
    induction fuel as [|fuel IH]; intros D A s ma mt aib slots i HII H48 Hma Hr Hi Hi0 Hf.
    { exfalso. pose proof (nfuel_pos A ma mt aib slots (is_wf _ _ _ _ _ _ (ii_is HII)) Hma Hr). lia. }
    pose proof (ii_is HII) as HIS. pose proof (is_wf _ _ _ _ _ _ HIS) as HW. pose proof (is_rep _ _ _ _ _ _ HIS) as HR.
    pose proof (is_win _ _ _ _ _ _ HIS) as HWIN. pose proof (is_env _ _ _ _ _ _ HIS) as HE. pose proof (is_grd _ _ _ _ _ _ HIS) as HG.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32 & _ & Hsc & Hlen & Hav & Hfd & _).
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hi32 : i < 32) by (unfold mt_cnt, mt_last in Hlen; pose proof (w_last_range (mt_w32 mt)); lia).
    assert (Hc32 : 0 <= mt_cnt mt <= 32) by (unfold mt_cnt, mt_last; pose proof (w_last_range (mt_w32 mt)); lia).
    assert (Hp32 : 2 ^ mt_cnt mt <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
    rewrite m_ntfree_unfold.
    apply ts_canary_load; [exact (envok_statics _ _ _ _ HE) | exact HWIN |].
    intros cb' Hcb'. unfold GRD in HG. rewrite HG in Hcb'. injection Hcb' as <-.
    cbv beta iota. rewrite at_Z. change (ma + 32) with (ma + moff FW32).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | exact Hw32 |].
    change (mt_f mt FW32) with (mt_w32 mt). rewrite at_Z. change (ma + 28) with (ma + moff FFreed).
    eapply (ts_lw_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | change (mt_f mt FFreed) with (mt_freed mt); lia |].
    change (Z_to_bv 64 (bv_swrap 32 (mt_f mt FFreed))) with (w32 (mt_freed mt)). rewrite at_Z. change (ma + 24) with (ma + moff FAvail).
    eapply (ts_lw_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | change (mt_f mt FAvail) with (mt_avail mt); lia |].
    change (Z_to_bv 64 (bv_swrap 32 (mt_f mt FAvail))) with (w32 (mt_avail mt)). cbv zeta.
    rewrite v_or_w32 by lia. rewrite v_sllw_1 by lia. rewrite (wsc_eq mt) by lia.
    apply (ts_nt_okcomp A s HW HR HWIN (eo_rodata _ _ _ _ HE) ma mt aib slots i Hma Hr Hi Hi0).
    intros ok Hok1 Hok2. destruct ok.
    - (* [comment removed for export] *)
      apply (ts_nt_freegrp sp0 argv envp cb D A s HII ma mt aib slots i Hma Hr Hi Hi0 (Hok1 eq_refl) H48 (m_nontrivial_free fuel)).
      { intros D' A' s' pa pm paib psl j HII' H48' Hpa Hpr Hj Hj0 Hlt.
        apply (IH D' A' s' pa pm paib psl j HII' H48' Hpa Hpr Hj Hj0). lia. }
      intros s' A' r HII' HF' HR' HRes' _.
      apply ts_canary_check; [exact (is_win _ _ _ _ _ _ (ii_is HII')) | exact (is_grd _ _ _ _ _ _ (ii_is HII')) |].
      apply ts_ret. exists A'. auto.
    - (* [comment removed for export] *)
      apply (ts_nt_keep sp0 argv envp cb D A s HII ma mt aib slots i Hma Hr Hi Hi0 (Hok2 eq_refl)).
      intros s' A' HII' HF' HR' HX HD.
      apply ts_canary_check; [exact (is_win _ _ _ _ _ _ (ii_is HII')) | exact (is_grd _ _ _ _ _ _ (ii_is HII')) |].
      apply ts_ret. exists A'. split; [exact HII'|]. split; [exact HF'|]. split; [exact HR'|]. left. auto.
  Qed.
End Main.

End WithLayout.
