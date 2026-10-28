(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRelSpec.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma arel_page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

Lemma map_contains_false_of_free : forall maps (addr n : word),
  (0 < bv_unsigned n)%Z ->
  region_free maps addr n = true -> map_contains maps addr n = false.
Proof.
  induction maps as [|[b s] maps IH]; intros addr n Hn Hf; [reflexivity|].
  cbn [region_free] in Hf. apply andb_true_iff in Hf. destruct Hf as [H1 H2].
  unfold map_contains. cbn [existsb fst snd]. fold (map_contains maps addr n).
  rewrite (IH addr n Hn H2). rewrite orb_false_r.
  unfold iv_overlap in H1. apply negb_true_iff in H1.
  apply Bool.not_true_is_false. intros Hc. apply andb_true_iff in Hc. destruct Hc as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2.
  apply andb_false_iff in H1. destruct H1 as [D | D]; apply Z.ltb_ge in D; lia.
Qed.

Lemma region_free_app_r : forall X1 X2 (a n : word),
  region_free (X1 ++ X2) a n = true -> region_free X2 a n = true.
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [exact H|].
  cbn in H. apply andb_true_iff in H. apply IH. tauto.
Qed.

Lemma region_free_app_l : forall X1 X2 (a n : word),
  region_free (X1 ++ X2) a n = true -> region_free X1 a n = true.
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [reflexivity|].
  cbn in H |- *. apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1. cbn. eapply IH; exact H2.
Qed.

Lemma mmap_fixed_rw_commit_outcome : forall addr len prot flags fd off i m o,
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
  mmap_err_out m o
  \/ (mmap_fixed_rw_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)) [])
  \/ (exists e, In e mmap_errnos
       /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                 (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption | reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. split; [exists tt; split; [exact Hb | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_fixed_rw_fresh_outcome : forall addr len prot flags fd off i m o,
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
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_noreserve_backed_ok flags m nZ = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_backing flags addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                      (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (arel_page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_fixed_noaccess_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_backing flags addr n
               (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                  ((addr, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (arel_page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_noreplace_rw_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = false ->
  mmap_noreplace_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_noreserve_backed_ok flags m nZ = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_backing flags addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                      (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna Hnrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna, Hnrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_noreplace_noaccess_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_backing flags addr n
               (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                  ((addr, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.
