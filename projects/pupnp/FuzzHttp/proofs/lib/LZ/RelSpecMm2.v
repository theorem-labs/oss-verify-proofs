(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RelSpec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma mmap_fixed_rw_outcome_raw : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (mmap_fixed_rw_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
               (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)) [])
  \/ exists e, In e mmap_errnos /\
       o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
              (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfx Hrw. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfx, Hrw. cbv zeta. cbn [negb].
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  rewrite Hrf, Hmc. cbn [negb andb]. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption| reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_fixed_rw_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_fixed_rw_budget_ok flags m addr n = true ->
  mmap_spec addr len prot flags fd off i m o /\ mmap_forced addr len prot flags fd off i m o <->
  mmap_err_out_when (mmap_fixed_commit_refusable flags m addr n) m o
  \/ (mmap_fixed_rw_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
               (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)) [])
  \/ exists e, In e mmap_destructive_errnos /\
       o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
              (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfx Hrw. cbv zeta. intros Hce Hal Hpos Hrf Hmc Hb.
  pose proof (fun o2 => mmap_fixed_rw_outcome_raw addr len prot flags fd off i m o2 Hoff Hanon Hlen Hmod Hna Hfx Hrw
                Hce Hal Hpos Hrf Hmc) as R.
  cbv zeta in R. unfold mmap_err_out_when, mmap_forced, mmap_fixed_commit_refusable. rewrite Hb. cbn [negb mmap_errnos_when].
  assert (Hrep : mmap_spec addr len prot flags fd off i m
    (Ok (mkEffect addr [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
       (with_mmap_replacement flags addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
          (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) m)) [])).
  { apply R. right; left. split; [exact Hb| reflexivity]. }
  assert (Hnr : forall e, In e mmap_errnos ->
    ~ (forall eff2 m2 evs2, mmap_spec addr len prot flags fd off i m (Ok eff2 m2 evs2) ->
         Run.ret_in_errnos mmap_errnos (eff_ret eff2) = true)).
  { intros e He Hall. pose proof (Hall _ _ _ Hrep) as Hx. cbn [eff_ret] in Hx.
    rewrite (mmap_errnos_aligned_false addr Hal) in Hx. discriminate Hx. }
  split.
  - intros [Hs Hf]. apply R in Hs as [(e & He & ->) | [(Hb' & ->) | (e & He & ->)]].
    + exfalso. exact (Hnr e He (Hf _ _ _ eq_refl (mmap_errnos_errno e He))).
    + right; left. split; [first [exact Hb'| reflexivity]| reflexivity].
    + exfalso. exact (Hnr e He (Hf _ _ _ eq_refl (mmap_errnos_errno e He))).
  - intros [(e & He & _) | [(Hb' & ->) | (e & He & _)]].
    + destruct He.
    + split; [exact Hrep|]. intros eff m' evs Hx Hr. apply Ok_inj in Hx as (<- & _ & _). cbn [eff_ret] in Hr.
      rewrite (mmap_errnos_aligned_false addr Hal) in Hr. discriminate Hr.
    + destruct He.
Qed.

Lemma mmap_fixed_rw_span_outcome_raw : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = false ->
  region_free (vm_reserved h ++ vm_maps h) addr n = false ->
  mmap_spec addr len prot flags fd off i m o <->
  (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (mmap_fixed_rw_span_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
               (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next h addr n) m)) [])
  \/ exists e, In e mmap_errnos /\
       o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
              (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfx Hrw. cbv zeta. intros Hce Hal Hpos Hrf Hmc Hnf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfx, Hrw. cbv zeta. cbn [negb].
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  rewrite Hrf, Hmc, Hnf. cbn [negb andb]. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption| reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_fixed_rw_span_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = false ->
  region_free (vm_reserved h ++ vm_maps h) addr n = false ->
  mmap_fixed_rw_span_budget_ok flags m addr n = true ->
  mmap_spec addr len prot flags fd off i m o /\ mmap_forced addr len prot flags fd off i m o <->
  mmap_err_out_when (mmap_fixed_span_refusable flags m addr n) m o
  \/ (mmap_fixed_rw_span_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
               (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next h addr n) m)) [])
  \/ exists e, In e mmap_destructive_errnos /\
       o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
              (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfx Hrw. cbv zeta. intros Hce Hal Hpos Hrf Hmc Hnf Hb.
  pose proof (fun o2 => mmap_fixed_rw_span_outcome_raw addr len prot flags fd off i m o2 Hoff Hanon Hlen Hmod Hna Hfx Hrw
                Hce Hal Hpos Hrf Hmc Hnf) as R.
  cbv zeta in R. unfold mmap_err_out_when, mmap_forced, mmap_fixed_span_refusable. rewrite Hb. cbn [negb mmap_errnos_when].
  assert (Hrep : mmap_spec addr len prot flags fd off i m
    (Ok (mkEffect addr [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
       (with_mmap_replacement flags addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
          (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) m)) [])).
  { apply R. right; left. split; [exact Hb| reflexivity]. }
  assert (Hnr : forall e, In e mmap_errnos ->
    ~ (forall eff2 m2 evs2, mmap_spec addr len prot flags fd off i m (Ok eff2 m2 evs2) ->
         Run.ret_in_errnos mmap_errnos (eff_ret eff2) = true)).
  { intros e He Hall. pose proof (Hall _ _ _ Hrep) as Hx. cbn [eff_ret] in Hx.
    rewrite (mmap_errnos_aligned_false addr Hal) in Hx. discriminate Hx. }
  split.
  - intros [Hs Hf]. apply R in Hs as [(e & He & ->) | [(Hb' & ->) | (e & He & ->)]].
    + exfalso. exact (Hnr e He (Hf _ _ _ eq_refl (mmap_errnos_errno e He))).
    + right; left. split; [first [exact Hb'| reflexivity]| reflexivity].
    + exfalso. exact (Hnr e He (Hf _ _ _ eq_refl (mmap_errnos_errno e He))).
  - intros [(e & He & _) | [(Hb' & ->) | (e & He & _)]].
    + destruct He.
    + split; [exact Hrep|]. intros eff m' evs Hx Hr. apply Ok_inj in Hx as (<- & _ & _). cbn [eff_ret] in Hr.
      rewrite (mmap_errnos_aligned_false addr Hal) in Hr. discriminate Hr.
    + destruct He.
Qed.

Lemma syscall_spec_233 : forall i m o,
  bv_unsigned (in_sysno i) = 233%Z ->
  syscall_spec i m o <-> madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma madvise_dontneed_outcome : forall addr len advice i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  madvise_dontneed_b advice = true ->
  w_is0 len = false ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ < two_pow_64)%Z ->
  madvise_dontneed_ok (m_vmmaps m) addr n = true ->
  madvise_spec addr len advice i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next m addr n) [].
Proof.
  intros addr len advice i m o Hal Hadv Hlen. cbv zeta. intros Hhi Hok.
  unfold madvise_spec. rewrite (proj2 (Z.eqb_eq _ _) Hal), Hadv, Hlen. cbn [negb].
  replace (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z with false by (symmetry; apply Z.leb_gt; exact Hhi).
  rewrite bind_get_model. cbv beta zeta. rewrite Hok. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
  - intros ->.
    first [ (eexists _, _, _, _; split; [reflexivity|]; split; reflexivity)
          | (eexists _, _, _, _; split; [reflexivity|]; split; [|reflexivity]; eexists _, _, _, _; repeat split; reflexivity)
          | (eexists _, _, _, _; split; [eexists _, _, _, _; repeat split; reflexivity|]; split; reflexivity) ].
Qed.
