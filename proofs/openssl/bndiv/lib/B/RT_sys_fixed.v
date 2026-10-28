(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA NodesA_mm ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct BackingAlgebra.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require AllocSim.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout RT_iface D_defs RT_state RT_rep RT_allowmain RT_sys_stmt RT_sys_img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reserved_free_above : forall (lo n : word), SEGTOP_A <= bv_unsigned lo ->
  region_free (segments_reserved bsegs) lo n = true.
Proof.
  intros lo n Hlo. apply region_free_intro. intros a sz Hin.
  pose proof (proj1 (Forall_forall _ _) asan_res_hull (a, sz) Hin) as (_ & H2). cbn [fst snd] in H2.
  unfold IMG_HI in H2. unfold SEGTOP_A in Hlo.
  unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge. lia.
Qed.

Lemma map_contains_intro : forall l (lo n : word) e, In e l ->
  bv_unsigned (fst e) <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
  map_contains l lo n = true.
Proof.
  intros l lo n e Hin H1 H2. unfold map_contains. apply existsb_exists. exists e. split; [exact Hin|].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_zero : forall l lo hi,
  Forall (fun q => B q + S q <= lo \/ hi <= B q) l -> overlap_sum l lo hi = 0.
Proof.
  induction l as [|q l IH]; intros lo hi H; [reflexivity|].
  inversion H as [|? ? Hq Hl]; subst. rewrite overlap_sum_cons, (iv_count_in_rng_disjoint q lo hi Hq), (IH lo hi Hl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_seps_in : forall l lo hi e, ForallOrdPairs iv_apart l -> In e l ->
  B e <= lo -> hi <= B e + S e -> lo <= hi -> overlap_sum l lo hi <= hi - lo.
Proof.
  induction l as [|p l IH]; intros lo hi e Hs Hin H1 H2 H3; [destruct Hin|].
  inversion Hs as [|? ? Hf Hs']; subst. rewrite overlap_sum_cons.
  destruct Hin as [Hpe|Hin].
  - subst e. rewrite overlap_sum_zero; [pose proof (iv_count_in_rng_le p lo hi H3); lia|].
    apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) Hf q Hq) as Hd.
    unfold iv_apart in Hd. unfold B, S in *. lia.
  - pose proof (proj1 (Forall_forall _ _) Hf e Hin) as Hd. unfold iv_apart in Hd.
    rewrite (iv_count_in_rng_disjoint p lo hi) by (unfold B, S in *; lia).
    specialize (IH lo hi e Hs' Hin H1 H2 H3). lia.
Qed.

(* [comment removed for export] *)
Lemma maps0_prb : forall L, layout_ok L -> In (Z_to_bv 64 (l_PRB L), Z_to_bv 64 0x2000011000) (l_maps0 L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & (HM & _ & _) & _).
  exact (proj1 (Forall_forall _ _) HM _ (or_introl eq_refl)).
Qed.

(* [comment removed for export] *)
Lemma maps0_shadow : forall L, layout_ok L ->
  In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000) (l_maps0 L) /\ In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) (l_maps0 L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & (HM & _ & _) & _).
  split.
  - exact (proj1 (Forall_forall _ _) HM (0x7fff7000, 0x10000000) ltac:(apply in_or_app; right; left; reflexivity)).
  - exact (proj1 (Forall_forall _ _) HM (0x2008fff7000, 0xdfff0001000) ltac:(apply in_or_app; right; right; right; left; reflexivity)).
Qed.

(* [comment removed for export] *)
Lemma artm_in_maps : forall Σ mo e, ARTM_A Σ mo -> In e (rt_maps Σ) -> In e (vm_maps (m_vmmaps mo)).
Proof.
  intros Σ mo e (HP & _) Hin. pose proof (Permutation_in _ (Permutation_sym HP) Hin) as H.
  apply List.filter_In in H as [H _]. exact H.
Qed.

Lemma l_maps0_in_rt_maps : forall Σ e, In e (l_maps0 (lay Σ)) -> In e (rt_maps Σ).
Proof. intros Σ e H. unfold rt_maps. apply in_or_app. right. exact H. Qed.

(* [comment removed for export] *)
Lemma covered_subtract_le : forall l lo hi x, ivs_wf l -> lo <= hi ->
  covered (maps_subtract l lo hi) x = true -> covered l x = true.
Proof. intros l lo hi x W H C. rewrite (covered_subtract l lo hi x W H) in C. apply andb_prop in C as [C _]. exact C. Qed.

(* [comment removed for export] *)
Lemma shadow_lazy_cut : forall mo mo' lo hi, model_ivs_wf mo -> lo <= hi -> shadow_lazy mo ->
  m_vm_lazy mo' = maps_subtract (m_vm_lazy mo) lo hi ->
  vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi ->
  (hi <= K_LOW_SHADOW_lo \/ K_LOW_SHADOW_hi <= lo /\ hi <= K_HIGH_SHADOW_lo \/ K_HIGH_SHADOW_hi <= lo) ->
  shadow_lazy mo'.
Proof.
  intros mo mo' lo hi Hwf Hlh Hsl El En Hoff a Ha.
  pose proof Hwf as (Wm & Wn & Wl & _).
  destruct (Hsl a Ha) as (L1 & N1).
  pose proof (page_base_facts' a) as (P1 & P2 & P3).
  rewrite El, En. split.
  - apply page_in_ranges_subtract_keep; [exact Wl | exact Hlh | | exact L1].
    clear - Ha Hoff P1 P2 P3. unfold shreg, Shadow.SHB, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *.
    destruct Ha as [Ha|Ha]; destruct Hoff as [Hoff|[Hoff|Hoff]]; Z.div_mod_to_equations; lia.
  - rewrite covered_subtract by assumption. rewrite N1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shadow_lazy_cut_nc : forall mo mo' lo hi, model_ivs_wf mo -> lo <= hi -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  shadow_lazy mo ->
  m_vm_lazy mo' = maps_subtract (m_vm_lazy mo) lo hi ->
  vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi ->
  (forall x, lo <= x < hi -> covered (m_vm_lazy mo) x = false) ->
  shadow_lazy mo'.
Proof.
  intros mo mo' lo hi Hwf Hlh Hlo Hhi Hsl El En Hnc a Ha.
  pose proof Hwf as (Wm & Wn & Wl & _).
  destruct (Hsl a Ha) as (L1 & N1).
  pose proof (page_base_facts' a) as (P1 & P2 & P3).
  rewrite El, En. split.
  - apply page_in_ranges_subtract_keep; [exact Wl | exact Hlh | | exact L1].
    destruct (Z_lt_le_dec (bv_unsigned (page_base a)) lo) as [H1|H1];
      [left; clear - H1 P3 Hlo; Z.div_mod_to_equations; lia|].
    destruct (Z_lt_le_dec (bv_unsigned (page_base a)) hi) as [H2|H2]; [|right; exact H2].
    exfalso. pose proof (page_in_ranges_covered _ _ L1) as C. rewrite (Hnc _ (conj H1 H2)) in C. discriminate.
  - rewrite covered_subtract by assumption. rewrite N1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma A_bytes_rtA_allow : forall Σ, layout_ok (lay Σ) -> A_bytes (aw Σ) <= CREDIT0 ->
  A_bytes (rtA_allow Σ) <= CREDIT0 + 2 ^ 36 + 2 ^ 35.
Proof.
  intros Σ HL Haw. unfold rtA_allow. rewrite !A_bytes_app.
  pose proof (A_bytes_allow_main (lay Σ) HL) as H1.
  assert (H2 : A_bytes (l_al0 (lay Σ)) <= 2 ^ 36).
  { unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & H & _). exact H. }
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem fixed_commit_ok : fixed_commit_node.
Proof.
  intros Σ Σ' PMc Pm K addr len HPMc _ EL Es Enr Eaw Heg Heg38 HL Haw Hlen Hlal Hal HSB Hend Hm.
  assert (EA : rtA_allow Σ' = rtA_allow Σ) by (unfold rtA_allow; rewrite Eaw, EL; reflexivity).
  assert (EM : rt_maps Σ' = rt_maps Σ) by (unfold rt_maps; rewrite Es, EL; reflexivity).
  unfold ASTA. cbn [rt_allow ARTM RTA]. rewrite EA.
  pose proof (maps0_prb _ HL) as HM0.
  (* [comment removed for export] *)
  pose proof HL as HL'. unfold layout_ok in HL'.
  destruct HL' as ((Hsp1 & Hsp2) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & (HSB1 & HSB2) & _).
  unfold l_ACEIL, STACK_WIN, sp_window_lo, sp_window_hi, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *.
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (A_bytes_rtA_allow Σ HL Haw) as HAB. unfold CREDIT0 in HAB.
  apply (ast_mmap_fixed_commit bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
           K (fun mo => ARTM_A Σ' mo /\ PMc mo) addr len).
  - lia.
  - lia.
  - unfold page_size. exact Hal.
  - intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). rewrite Hrd.
    repeat (split; [assumption|]). exact S7.
  - intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
    rewrite Hrd.
    assert (Eua : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; lia).
    assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    assert (Hin7 : In (Z_to_bv 64 (l_PRB (lay Σ)), Z_to_bv 64 0x2000011000) (vm_maps (m_vmmaps mo)))
      by (apply (artm_in_maps Σ mo _ HA), l_maps0_in_rt_maps; exact HM0).
    assert (E7a : bv_unsigned (Z_to_bv 64 (l_PRB (lay Σ))) = l_PRB (lay Σ)) by (apply unsigned_lit; lia).
    assert (E7n : bv_unsigned (Z_to_bv 64 0x2000011000) = 0x2000011000) by (apply unsigned_lit; lia).
    assert (Hov : overlap_sum (vm_maps (m_vmmaps mo)) addr (addr + len) <= len).
    { pose proof (overlap_sum_seps_in (vm_maps (m_vmmaps mo)) addr (addr + len) _ Hsep Hin7) as Hov.
      unfold B, S in Hov. cbn [fst snd] in Hov. rewrite E7a, E7n in Hov. specialize (Hov ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
    split; [exact Hwf|].
    split; [unfold alloc_top, stack_max_size; rewrite Hisp; lia|].
    split; [rewrite Eres; apply reserved_free_above; rewrite Eua; unfold SEGTOP_A; lia|].
    split; [apply (map_contains_intro _ _ _ _ Hin7); cbn [fst snd]; rewrite ?Eua, ?Eul, ?E7a, ?E7n; lia|].
    split; [rewrite Elim; unfold E0_MAX, VMLIMIT in *; lia|].
    split.
    + (* [comment removed for export] *)
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_maps]; rewrite EM; exact Hperm|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_reserved]; exact Eres|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_limit]; exact Elim|].
      split.
      { pose proof (eager_used_fixed50_le mo (Z_to_bv 64 addr) (Z_to_bv 64 len) Hwf) as Hle. rewrite Eua, Eul in Hle. lia. }
      (* [comment removed for export] *)
      pose proof Hwf as (Wm & Wn & Wl & _).
      split; [apply model_ivs_wf_fixed; [exact Hwf| rewrite Eua, Eul; lia]|].
      split; [apply (lazy_in_maps_fixed50 mo _ _ Hwf Hlz)|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_maps]; exact Hsep|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_init_sp]; rewrite EL; exact Hisp|].
      split.
      { intros z Hz. rewrite EL. apply Hcf. rewrite mdl_fixed_vmmaps, mdl_fixed_lazy50 in Hz. unfold mmap_fixed_rw_next in Hz.
        cbn [vm_noaccess] in Hz. rewrite covered_app in Hz |- *. rewrite Eua, Eul in Hz.
        apply orb_true_iff in Hz as [Hz|Hz]; apply orb_true_iff;
          [left; refine (covered_subtract_le _ _ _ _ Wn _ Hz); lia | right; refine (covered_subtract_le _ _ _ _ Wl _ Hz); lia]. }
      split.
      { apply (shadow_lazy_cut mo _ addr (addr + len) Hwf ltac:(lia) Hsl).
        - rewrite mdl_fixed_lazy50, Eua, Eul. reflexivity.
        - rewrite mdl_fixed_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite Eua, Eul. reflexivity.
        - unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia. }
      (* [comment removed for export] *)
      split; [unfold maps_zbound; rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_maps]; exact Hzb|].
      apply NodesA_madv.noaccess_pos_fixed; [exact Hwf| exact Hnp].
    + apply (HPMc mo); [apply mdl_fixed_fds| apply mdl_fixed_fs| exact HPc].
  - intros mo (HA & _). pose proof HA as (_ & _ & _ & _ & (_ & _ & _ & Hisp & _)). unfold alloc_top, stack_max_size. rewrite Hisp. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma maps0_pab : forall L, layout_ok L -> In (Z_to_bv 64 (l_PAB L), Z_to_bv 64 0x800000) (l_maps0 L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & (HM & _ & _) & _).
  exact (proj1 (Forall_forall _ _) HM (l_PAB L, 0x800000) ltac:(apply in_or_app; left; right; left; reflexivity)).
Qed.

Theorem fixed_commit_pab_ok : fixed_commit_pab_node.
Proof.
  intros Σ Σ' PMc Pm K addr len HPMc _ EL Es Eaw Heg Heg38 HL Haw Hlen Hlal Hal HSB Hend Hm.
  assert (EA : rtA_allow Σ' = rtA_allow Σ) by (unfold rtA_allow; rewrite Eaw, EL; reflexivity).
  assert (EM : rt_maps Σ' = rt_maps Σ) by (unfold rt_maps; rewrite Es, EL; reflexivity).
  unfold ASTA. cbn [rt_allow ARTM RTA]. rewrite EA.
  pose proof (maps0_pab _ HL) as HM0.
  pose proof HL as HL'. unfold layout_ok in HL'.
  destruct HL' as ((Hsp1 & Hsp2) & _ & _ & _ & _ & _ & _ & (Q1 & Q2 & Q3 & Q4 & Q5) & _).
  unfold l_ACEIL, STACK_WIN, sp_window_lo, sp_window_hi, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *.
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (A_bytes_rtA_allow Σ HL Haw) as HAB. unfold CREDIT0 in HAB.
  apply (ast_mmap_fixed_commit bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
           K (fun mo => ARTM_A Σ' mo /\ PMc mo) addr len).
  - lia.
  - lia.
  - unfold page_size. exact Hal.
  - intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). rewrite Hrd.
    repeat (split; [assumption|]). exact S7.
  - intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
    rewrite Hrd.
    assert (Eua : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; lia).
    assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    assert (Hin9 : In (Z_to_bv 64 (l_PAB (lay Σ)), Z_to_bv 64 0x800000) (vm_maps (m_vmmaps mo)))
      by (apply (artm_in_maps Σ mo _ HA), l_maps0_in_rt_maps; exact HM0).
    assert (E9a : bv_unsigned (Z_to_bv 64 (l_PAB (lay Σ))) = l_PAB (lay Σ)) by (apply unsigned_lit; lia).
    assert (E9n : bv_unsigned (Z_to_bv 64 0x800000) = 0x800000) by (apply unsigned_lit; lia).
    assert (Hov : overlap_sum (vm_maps (m_vmmaps mo)) addr (addr + len) <= len).
    { pose proof (overlap_sum_seps_in (vm_maps (m_vmmaps mo)) addr (addr + len) _ Hsep Hin9) as Hov.
      unfold B, S in Hov. cbn [fst snd] in Hov. rewrite E9a, E9n in Hov. specialize (Hov ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
    split; [exact Hwf|].
    split; [unfold alloc_top, stack_max_size; rewrite Hisp; lia|].
    split; [rewrite Eres; apply reserved_free_above; rewrite Eua; unfold SEGTOP_A; lia|].
    split; [apply (map_contains_intro _ _ _ _ Hin9); cbn [fst snd]; rewrite ?Eua, ?Eul, ?E9a, ?E9n; lia|].
    split; [rewrite Elim; unfold E0_MAX, VMLIMIT in *; lia|].
    split.
    + split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_maps]; rewrite EM; exact Hperm|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_reserved]; exact Eres|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_limit]; exact Elim|].
      split.
      { pose proof (eager_used_fixed50_le mo (Z_to_bv 64 addr) (Z_to_bv 64 len) Hwf) as Hle. rewrite Eua, Eul in Hle. lia. }
      pose proof Hwf as (Wm & Wn & Wl & _).
      split; [apply model_ivs_wf_fixed; [exact Hwf| rewrite Eua, Eul; lia]|].
      split; [apply (lazy_in_maps_fixed50 mo _ _ Hwf Hlz)|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_maps]; exact Hsep|].
      split; [rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_init_sp]; rewrite EL; exact Hisp|].
      split.
      { intros z Hz. rewrite EL. apply Hcf. rewrite mdl_fixed_vmmaps, mdl_fixed_lazy50 in Hz. unfold mmap_fixed_rw_next in Hz.
        cbn [vm_noaccess] in Hz. rewrite covered_app in Hz |- *. rewrite Eua, Eul in Hz.
        apply orb_true_iff in Hz as [Hz|Hz]; apply orb_true_iff;
          [left; refine (covered_subtract_le _ _ _ _ Wn _ Hz); lia | right; refine (covered_subtract_le _ _ _ _ Wl _ Hz); lia]. }
      split.
      { apply (shadow_lazy_cut mo _ addr (addr + len) Hwf ltac:(lia) Hsl).
        - rewrite mdl_fixed_lazy50, Eua, Eul. reflexivity.
        - rewrite mdl_fixed_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite Eua, Eul. reflexivity.
        - unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia. }
      (* [comment removed for export] *)
      split; [unfold maps_zbound; rewrite mdl_fixed_vmmaps; unfold mmap_fixed_rw_next; cbn [vm_maps]; exact Hzb|].
      apply NodesA_madv.noaccess_pos_fixed; [exact Hwf| exact Hnp].
    + apply (HPMc mo); [apply mdl_fixed_fds| apply mdl_fixed_fs| exact HPc].
  - intros mo (HA & _). pose proof HA as (_ & _ & _ & _ & (_ & _ & _ & Hisp & _)). unfold alloc_top, stack_max_size. rewrite Hisp. lia.
Qed.
