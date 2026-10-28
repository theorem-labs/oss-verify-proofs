(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA NodesA_mm ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct BackingAlgebra.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require AsanPlanCore AsanTablesB AsanPlanSound AsanPlanImagesB AsanNodesMmLib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Unforced.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs RT_state RT_rep RT_init RT_sys_stmt RT_sys_fixed RT_sys_munmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma live_bytes_app' : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a s] l1 IH]; intros l2; cbn [app live_bytes]; [lia| rewrite IH; lia]. Qed.

Lemma live_bytes_perm : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof.
  intros l l' H. induction H as [|[a s] l l' _ IH|[a s] [b t] l|l l' l'' _ IH1 _ IH2]; cbn [live_bytes]; lia.
Qed.

Lemma live_bytes_filter_vpos : forall l, live_bytes (List.filter vpos l) = live_bytes l.
Proof.
  induction l as [|[a s] l IH]; [reflexivity|]. cbn [List.filter]. destruct (vpos (a, s)) eqn:E; cbn [live_bytes]; rewrite IH; [lia|].
  unfold vpos in E. cbn [snd] in E. apply Z.ltb_ge in E. pose proof (bv_unsigned_in_range _ s) as R. unfold bv_modulus in R. lia.
Qed.

Lemma sum_cls_nonneg : forall f k, (forall c, 1 <= c <= Z.of_nat k -> 0 <= f c) -> 0 <= sum_cls f k.
Proof.
  intros f k. induction k as [|k IH]; intros H; cbn [sum_cls]; [lia|].
  pose proof (H (Z.of_nat (Datatypes.S k)) ltac:(lia)). specialize (IH ltac:(intros c Hc; apply H; lia)). lia.
Qed.

Lemma secmaps_bytes : forall Σ, rt_wf Σ -> live_bytes (map secmap (rev (sec Σ))) <= rt_eager Σ.
Proof.
  intros Σ HW. pose proof HW as (_ & (R1 & _) & _ & (S1 & S2 & _ & S4 & _) & _).
  assert (Hcls : 0 <= sum_cls (fun c => r_muser (pr Σ c) + r_mfa (pr Σ c)) 31).
  { apply sum_cls_nonneg. intros c Hc. destruct (R1 c ltac:(lia)) as ((M1 & _) & _ & _ & _ & (F1 & _) & _). lia. }
  assert (Hnres : 0 <= sec_nres Σ) by (destruct S2 as [E|E]; rewrite E; lia).
  unfold rt_eager.
  assert (H : live_bytes (map secmap (rev (sec Σ))) <= fold_right (fun s acc => smsz (s_n s) + acc) 0 (sec Σ)).
  { assert (HF : Forall (fun s => 0 <= smsz (s_n s)) (sec Σ)).
    { apply Forall_forall. intros s Hs. unfold smsz, pg_up, needed, rounded, rz_size.
      assert (X1 : 0 <= (Z.max (Z.max (s_n s) 1) 8 + 7) / 8) by (apply Z.div_pos; lia).
      assert (X2 : 0 <= 2 ^ rz_log (s_n s)) by (apply Z.pow_nonneg; lia).
      assert (X3 : 0 <= (8 * ((Z.max (Z.max (s_n s) 1) 8 + 7) / 8) + 16 * 2 ^ rz_log (s_n s) + 4095) / 4096) by (apply Z.div_pos; lia).
      lia. }
    clear -HF. rewrite map_rev.
    assert (E : forall l, live_bytes (rev l) = live_bytes l)
      by (intros l; apply live_bytes_perm; apply Permutation_sym, Permutation_rev).
    rewrite E. induction (sec Σ) as [|s ss IH]; cbn [map live_bytes fold_right secmap fst snd]; [lia|].
    inversion HF as [|? ? Hs Hss]; subst. specialize (IH Hss).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. pose proof (Z.mod_le (smsz (s_n s)) (bv_modulus 64) Hs ltac:(unfold bv_modulus; lia)). lia. }
  lia.
Qed.

Lemma rt_wf_budget : forall Σ, rt_wf Σ -> A_bytes (aw Σ) <= CREDIT0 /\ rt_eager Σ <= 2 ^ 38.
Proof. intros Σ HW. pose proof HW as (_ & _ & _ & _ & _ & _ & (B1 & _ & B3 & B4 & _) & _). lia. Qed.

Lemma rt_wf_nsec : forall Σ, rt_wf Σ -> Z.of_nat (length (sec Σ)) <= SEC_MAX.
Proof. intros Σ HW. pose proof HW as (_ & _ & _ & (S1 & _) & _). exact S1. Qed.

Lemma maps0_bounds : forall L, layout_ok L -> Z.of_nat (length (l_maps0 L)) <= 64 /\ live_bytes (l_maps0 L) <= 2 ^ 45.
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & H1 & H2) & _). lia.
Qed.

Lemma ledger_gap : forall Σ mo len, rt_wf Σ -> ARTM_A Σ mo -> 0 < len -> len mod 4096 = 0 -> len <= 2 ^ 32 ->
  vm_gap_available (m_vmmaps mo) len = true.
Proof.
  intros Σ mo len HW HA Hlen Hal Hsz. pose proof HA as (Hperm & Eres & _ & _ & (_ & _ & _ & Hisp & _ & _ & Hzb)).
  unfold maps_zbound in Hzb.
  pose proof HW as (HL & _). pose proof (rt_wf_budget _ HW) as (_ & Heg). pose proof (rt_wf_nsec _ HW) as Hns.
  pose proof (maps0_bounds _ HL) as (Hn0 & Hb0). pose proof (secmaps_bytes _ HW) as Hsb.
  pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  set (h := m_vmmaps mo) in *. set (L := vm_reserved h ++ vm_maps h).
  assert (HLb : live_bytes L <= 0x6d0000 + 2 ^ 38 + 2 ^ 45).
  { unfold L. rewrite live_bytes_app', Eres, RT_init.live_bytes_sum_sizes, AsanPlanImagesB.asan_res_sizes.
    rewrite <- (live_bytes_filter_vpos (vm_maps h)).
    rewrite (live_bytes_perm _ _ Hperm). unfold rt_maps. rewrite live_bytes_app'. lia. }
  assert (HLn : Z.of_nat (length L) <= 4 + SEC_MAX + 64 + 1).
  { unfold L. rewrite length_app, Eres, AsanPlanImagesB.asan_res_len. cbn [AsanPlanCore.APC.n_res AsanTablesB.ASAN_B].
    rewrite (Permutation_length Hperm) in Hzb. unfold rt_maps in Hzb.
    rewrite length_app, length_map, length_rev in Hzb. lia. }
  assert (Htop : alloc_top h = l_sp0 (lay Σ) - 2 ^ 23) by (unfold alloc_top, stack_max_size; rewrite Hisp; lia).
  unfold sp_window_lo, sp_window_hi, SEC_MAX in *.
  destruct (Unforced.gap_exists L len 4096 (alloc_top h) ltac:(lia) ltac:(lia) ltac:(rewrite Htop; lia)
              ltac:(reflexivity) ltac:(rewrite Unforced.gap_weight_sizes; nia))
    as (g & Hgal & HgF & Hgtop & Hgfree).
  apply (proj2 (vm_gap_available_iff h len)). exists (Z_to_bv 64 g).
  rewrite unsigned_lit by (rewrite Htop in Hgtop; lia).
  split; [exact Hgal|]. split; [lia|]. split; [exact Hgtop|]. exact Hgfree.
Qed.

Lemma region_free_apart : forall l (lo n : word) e, region_free l lo n = true -> In e l ->
  apart (bv_unsigned lo) (bv_unsigned n) (bv_unsigned (fst e)) (bv_unsigned (snd e)).
Proof.
  intros l lo n [b s] H Hin. pose proof (region_free_In _ _ _ _ _ H Hin) as X. unfold iv_overlap in X. cbn [fst snd].
  unfold apart. apply andb_false_iff in X as [X|X]; apply Z.ltb_ge in X; lia.
Qed.

Lemma maps0_e3 : forall L, layout_ok L -> In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000) (l_maps0 L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HM & _ & _) & _).
  exact (proj1 (Forall_forall _ _) HM (0x8fff7000, 0x20000000000) ltac:(apply in_or_app; right; right; left; reflexivity)).
Qed.

Section Placement.
Variables (Σ : rtsA) (mo : Model) (len : Z) (a : word).
Hypothesis HW : rt_wf Σ.
Hypothesis HA : ARTM_A Σ mo.
Hypothesis Hlen : 0 < len < 2 ^ 64.
Hypothesis Hg : (bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + len <= alloc_top (m_vmmaps mo))
  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 len) = true.

Lemma grant_apart_maps : forall e, In e (vm_maps (m_vmmaps mo)) -> apart (bv_unsigned a) len (bv_unsigned (fst e)) (bv_unsigned (snd e)).
Proof using Hlen Hg.
  intros e He. destruct Hg as (_ & _ & _ & Hf). pose proof (region_free_apart _ _ _ e Hf ltac:(apply in_or_app; right; exact He)) as X.
  rewrite unsigned_lit in X by lia. exact X.
Qed.

Lemma grant_placement : sgrant_ok Σ (bv_unsigned a) len.
Proof using HW HA Hlen Hg.
  pose proof HW as (HL & _). pose proof HA as (Hperm & Eres & _ & _ & (_ & _ & _ & Hisp & _)).
  destruct Hg as (G1 & G2 & G3 & G4).
  pose proof (maps0_shadow _ HL) as (HE2 & HE4). pose proof (maps0_e3 _ HL) as HE3.
  assert (Hin : forall e, In e (l_maps0 (lay Σ)) -> In e (vm_maps (m_vmmaps mo)))
    by (intros e He; exact (artm_in_maps Σ mo e HA (l_maps0_in_rt_maps Σ e He))).
  pose proof (grant_apart_maps _ (Hin _ HE2)) as D2. pose proof (grant_apart_maps _ (Hin _ HE3)) as D3.
  pose proof (grant_apart_maps _ (Hin _ HE4)) as D4.
  cbn [fst snd] in D2, D3, D4. rewrite !unsigned_lit in D2, D3, D4 by lia. unfold apart in D2, D3, D4.
  split.
  - unfold grant_ok. split; [exact G2|]. split; [unfold page_size in G1; exact G1|].
    split; [unfold l_ACEIL, STACK_WIN; unfold alloc_top, stack_max_size in G3; rewrite Hisp in G3; lia|].
    split; [unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi; lia|].

    destruct (Z_le_gt_dec (bv_unsigned a + len) 0x10000) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec SEGTOP_A (bv_unsigned a)) as [Y|Y]; [right; exact Y|]. exfalso.
    pose proof AsanPlanImagesB.asan_hull_cover as (_ & HC).
    cbn [AsanPlanCore.APC.img_lo AsanPlanCore.APC.img_hi AsanTablesB.ASAN_B] in HC. unfold SEGTOP_A in Y.
    destruct (HC (Z.max (bv_unsigned a) 0x10000) ltac:(lia)) as (iv & Hiv & Z1 & Z2).
    pose proof (region_free_apart _ _ _ iv G4 ltac:(apply in_or_app; left; rewrite Eres; exact Hiv)) as D.
    rewrite unsigned_lit in D by lia. unfold apart in D. lia.
  - apply Forall_forall. intros e He. exact (grant_apart_maps e (artm_in_maps Σ mo e HA He)).
Qed.
End Placement.

Theorem grant_node_ok : grant_node.
Proof.
  intros Σ Σ' PMc Pm K len HPMc _ HW Hlen Hlal Hsz Heg HΣ' Hm.
  pose proof HW as (HL & _). pose proof (rt_wf_budget _ HW) as (Haw & Heg38).
  pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  unfold sp_window_lo, sp_window_hi in *.
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (A_bytes_rtA_allow Σ HL Haw) as HAB. unfold CREDIT0 in HAB.
  assert (EA : forall P, rtA_allow (Σ' P) = rtA_allow Σ).
  { intros P. destruct (HΣ' P) as (EL & Eaw & _). unfold rtA_allow. rewrite Eaw, EL. reflexivity. }
  unfold ASTA. cbn [rt_allow ARTM RTA].
  eapply (cps_conseq bsegs).
  - apply (ast_mmap_anon_rw bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
             (fun a => sgrant_ok Σ (bv_unsigned a) len) (fun a => K (bv_unsigned a))
             (fun a mo => ARTM_A (Σ' (bv_unsigned a)) mo /\ PMc mo) len).
    + lia.
    + intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4 & S5 & S6). repeat (split; [assumption|]).
      intros a Ha. rewrite Hrd. pose proof (S6 (bv_unsigned a) Ha) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
    + intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
      rewrite Hrd.
      split; [exact Hwf|]. split; [exact Hlz|]. split; [exact (ledger_gap Σ mo len HW HA Hlen Hlal Hsz)|].
      split; [rewrite Elim; unfold E0_MAX, VMLIMIT in *; lia|].
      intros a Ha. destruct Ha as (G1 & G2 & G3 & G4 & G5).
      assert (Hg : (bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + len <= alloc_top (m_vmmaps mo))
                   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 len) = true)
        by (repeat split; assumption).
      split; [exact (grant_placement Σ mo len a HW HA ltac:(lia) Hg)|].
      destruct (HΣ' (bv_unsigned a)) as (EL & Eaw & Hperm' & Heg1 & Heg2).
      assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
      assert (Han : bv_unsigned a + bv_unsigned (Z_to_bv 64 len) <= 2 ^ 64).
      { rewrite Eul. unfold alloc_top, stack_max_size in G3. rewrite Hisp in G3. lia. }
      split.
      *
        split.
        { rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps]. rewrite filter_cons_pos by (cbn [snd]; rewrite Eul; lia).
          apply (Permutation_trans (l' := (a, Z_to_bv 64 len) :: rt_maps Σ)).
          - constructor. exact Hperm.
          - apply Permutation_sym. rewrite Z_to_bv_bv_unsigned in Hperm'. exact Hperm'. }
        split; [rewrite mdl_mmap_rw_vmmaps; cbn [vm_reserved]; exact Eres|].
        split; [rewrite mdl_mmap_rw_vmmaps; cbn [vm_limit]; exact Elim|].
        split.
        { pose proof (eager_used_mmap_rw_le mo a (Z_to_bv 64 len) (proj1 Hwf) Han) as Hle. rewrite Eul in Hle. lia. }
        split; [exact (model_ivs_wf_mmap_rw mo a _ Hwf Han)|].
        split; [exact (lazy_in_maps_mmap_rw mo a _ Hlz)|].
        split.
        { rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps]. constructor; [|exact Hsep].
          apply Forall_forall. intros e He. pose proof (grant_apart_maps mo len a ltac:(lia) Hg e He) as D.
          unfold apart in D. unfold iv_apart. cbn [fst snd]. rewrite Eul. lia. }
        split; [rewrite mdl_mmap_rw_vmmaps; cbn [vm_init_sp]; rewrite EL; exact Hisp|].
        split.
        { intros z Hz. rewrite EL. apply Hcf. rewrite mdl_mmap_rw_vmmaps, mdl_mmap_rw_lazy in Hz. cbn [vm_noaccess] in Hz. exact Hz. }

        split.
        { intros x Hx. rewrite mdl_mmap_rw_lazy, mdl_mmap_rw_vmmaps. cbn [vm_noaccess]. exact (Hsl x Hx). }

        split; [|apply NodesA_madv.noaccess_pos_mmap_rw; exact Hnp].
        unfold maps_zbound in Hzb |- *. rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps].
        rewrite filter_cons_pos by (cbn [snd]; rewrite Eul; lia). cbn [length]. rewrite !Nat2Z.inj_succ. clear - Hzb. lia.
      * apply (HPMc mo); [apply mdl_mmap_rw_fds| apply mdl_mmap_rw_fs| exact HPc].
    + intros mo (HA & _). pose proof HA as (_ & _ & _ & _ & (_ & _ & _ & Hisp & _)). unfold alloc_top, stack_max_size. rewrite Hisp. lia.
  - intros c Hc. exact Hc.
  - intros c (a & Ha & Hc). exists (bv_unsigned a). split; [exact Ha|]. rewrite (EA (bv_unsigned a)). exact Hc.
Qed.

End GWIN.
