(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Cfg ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import MmapComplete.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Placement.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errno_of_None_not_errno : forall r es, errno_of r = None -> errno_ret_in es r = true ->
  errnos_ok es = true -> False.
Proof.
  intros r es Hn Hin Hok. apply errno_ret_in_true in Hin as (e & HIn & ->).
  pose proof (errnos_ok_range es e Hok HIn) as [H1 H2].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<9281341881.7000007S2H12H2".
rewrite errno_of_errno_ret in Hn by lia. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma errno_ret_in_nil : forall r, errno_ret_in [] r = false.
Proof. reflexivity. Qed.

Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof. reflexivity. Qed.

Lemma mmap_destructive_errnos_nil : mmap_destructive_errnos = [].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma errno_ret_in_when : forall b r, errno_ret_in (mmap_errnos_when b) r = true -> b = true /\ r = errno_ret ENOMEM.
Proof.
  intros [|] r H; [|rewrite mmap_errnos_when_false, errno_ret_in_nil in H; discriminate].
  split; [reflexivity|]. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity.
Qed.

Lemma errno_ret_in_mprotect_when : forall b r,
  errno_ret_in (mprotect_errnos_when b) r = true -> b = true /\ r = errno_ret ENOMEM.
Proof.
  intros [|] r H; [|cbn in H; discriminate].
  split; [reflexivity|]. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma errno_of_below_top : forall r h nZ, 0 <= nZ -> bv_unsigned r + nZ <= alloc_top h -> errno_of r = None.
Proof.
  intros r h nZ Hn Hb. pose proof (alloc_top_room h) as R. unfold two_pow_64, stack_max_size in R.
  apply errno_of_small. Local Ltac2 Set LiaHints.tbl := fun () => "0010=64342160945.6000009S2Hn2Hb1R".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma bv_eqb_errno_small : forall e (aw : word), errno_of aw = None -> 1 <= e <= 4095 ->
  bv_eqb (errno_ret e) aw = false.
Proof.
  intros e aw Hn He. destruct (bv_eqb (errno_ret e) aw) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. Local Ltac2 Set LiaHints.tbl := fun () => "0010<9283400460.5000004S2He".
rewrite <- E, errno_of_errno_ret in Hn by lia. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma page_round_up_Z_nonneg' : forall z, 0 <= z -> 0 <= page_round_up_Z z.
Proof. intros z Hz. unfold page_round_up_Z, page_size. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]. Qed.

Lemma page_size_4096 : page_size = 4096.
Proof. reflexivity. Qed.

Lemma errno_ret_in_mmap_ENOMEM : errno_ret_in mmap_errnos (errno_ret ENOMEM) = true.
Proof. unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma errno_ret_in_mprotect_ENOMEM : errno_ret_in mprotect_errnos (errno_ret ENOMEM) = true.
Proof. unfold errno_ret_in, mprotect_errnos. cbn [existsb]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma errno_ret_in_mmap_inv : forall r, errno_ret_in mmap_errnos r = true -> r = errno_ret ENOMEM.
Proof. intros r H. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity. Qed.

Lemma errno_ret_in_mprotect_inv : forall r, errno_ret_in mprotect_errnos r = true -> r = errno_ret ENOMEM.
Proof. intros r H. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity. Qed.

Lemma errno_ret_in_mmap_small : forall r, errno_of r = None -> errno_ret_in mmap_errnos r = false.
Proof.
  intros r Hn. destruct (errno_ret_in mmap_errnos r) eqn:E; [|reflexivity].
  exfalso. exact (errno_of_None_not_errno r mmap_errnos Hn E eq_refl).
Qed.

Lemma errno_ret_in_mprotect_small : forall r, errno_of r = None -> errno_ret_in mprotect_errnos r = false.
Proof.
  intros r Hn. destruct (errno_ret_in mprotect_errnos r) eqn:E; [|reflexivity].
  exfalso. exact (errno_of_None_not_errno r mprotect_errnos Hn E eq_refl).
Qed.

Lemma region_free_app_l : forall l1 l2 lo n, region_free (l1 ++ l2) lo n = true -> region_free l1 lo n = true.
Proof.
  induction l1 as [|[b s] r IH]; intros l2 lo n H; [reflexivity|].
  cbn [app region_free] in *. apply andb_prop in H as [H1 H2]. rewrite H1, (IH l2 lo n H2). reflexivity.
Qed.

Lemma nstep_mmap_grant_no_errno : forall addr len prot flags mo eff mo' evs eg mg evg,
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo = CheckOk mg evg ->
  errno_ret_in mmap_errnos (eff_ret eg) = false ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs eg mg evg H Hg Hng.
  apply nstep_mmap_iff in H as (_ & _ & Hns).
  pose proof (proj1 (check_syscall_ok_iff (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot;
                                                         Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]) eg mo mg evg)) as Hs.
  rewrite check_syscall_mmap in Hs by reflexivity. specialize (Hs Hg).
  pose proof (fun Hoff => nonspurious_not_refusal_of_grant ACFG _ mo eff eg mg evg Hoff Hns Hs) as X.
  specialize (X ltac:(apply acfg_family_off_222; reflexivity)).
  rewrite !refusal_b_222 in X by reflexivity. exact (X Hng).
Qed.

Lemma nstep_mprotect_grant_no_errno : forall addr len prot mo eff mo' evs eg mg evg,
  nstep (NMprotect addr len prot) mo eff mo' evs ->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eg mo = CheckOk mg evg ->
  errno_ret_in mprotect_errnos (eff_ret eg) = false ->
  errno_ret_in mprotect_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot mo eff mo' evs eg mg evg H Hg Hng.
  apply nstep_mprotect_iff in H as (_ & Hns).
  pose proof (proj1 (check_syscall_ok_iff (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) eg mo mg evg)) as Hs.
  rewrite check_syscall_mprotect in Hs by reflexivity. specialize (Hs Hg).
  pose proof (fun Hoff => nonspurious_not_refusal_of_grant ACFG _ mo eff eg mg evg Hoff Hns Hs) as X.
  specialize (X ltac:(apply acfg_family_off_226; reflexivity)).
  rewrite !refusal_b_226 in X by reflexivity. exact (X Hng).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gap_available_of_free_base : forall h nZ g,
  0 <= nZ -> g mod 4096 = 0 -> 0 < g -> g + nZ <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ g Hn Hal Hpos Htop Hfree. pose proof (alloc_top_lt h) as T. unfold two_pow_64 in T.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=44930864010.900000@S2Hn4Hpos4Htop1T".
assert (Hg : bv_unsigned (Z_to_bv 64 g) = g) by (apply unsigned_lit; lia).
  apply (MmapComplete.vm_gap_available_complete h nZ (Z_to_bv 64 g)); rewrite ?Hg; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma grant_refusable_false_intro : forall flags m nZ,
  mmap_noreserve_b flags = false ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m) ->
  vm_gap_available (m_vmmaps m) nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ Hnr Hb Hg. unfold mmap_grant_refusable, mmap_noreserve_backed_ok.
  rewrite Hnr, Hg. rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.

Lemma reserve_refusable_false_intro : forall m nZ,
  vm_gap_available (m_vmmaps m) nZ = true -> mmap_reserve_refusable m nZ = false.
Proof. intros m nZ Hg. unfold mmap_reserve_refusable. rewrite Hg. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AnonMmap.
Variables (addr len prot flags : Z).
Hypothesis Hlen : 0 < len < 2^64.

Let lenw := Z_to_bv 64 len.
Let nZ := mmap_len len.

#[using="Hlen"] Lemma anon_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ.
Proof.
  split.
  - subst lenw. Local Ltac2 Set LiaHints.tbl := fun () => "0030=2018122316.6 65116886348.565121635256.600000600<00BS4HlenS4HlenS4Hlen".
rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - subst lenw nZ. rewrite unsigned_lit by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Hlen lenw"] Lemma anon_rw_grant : forall mo,
  negb (mmap_anon_b (Z_to_bv 64 flags)) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = false ->
  exists eg mg, check_mmap (Z_to_bv 64 addr) lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo G2 Hshape R. destruct anon_len_facts as [L0 L1].
  unfold mmap_grant_refusable in R. apply orb_false_iff in R as [R1 R2]. apply negb_false_iff in R1, R2.
  destruct (vm_gap_available_find _ _ R2) as [b Hfind].
  destruct (vm_find_base_sound _ _ _ Hfind) as (B1 & B2 & B3 & B4).
  pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
  assert (NB : errno_ret_in mmap_errnos b = false)
    by (apply errno_ret_in_mmap_small; apply (errno_of_below_top b (m_vmmaps mo) nZ); [lia | exact B3]).
  exists (mkEffectU b [] [(b, Z_to_bv 64 nZ)] [] [] []). eexists. split; [|exact NB].
  unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
  rewrite G2, L0, Hshape. cbv iota beta. rewrite NB. cbv zeta. rewrite L1.
  rewrite (proj2 (Z.eqb_eq _ _) B1), (proj2 (Z.ltb_lt _ _) B2), (proj2 (Z.leb_le _ _) B3), B4, R1.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

#[using="Hlen lenw"] Lemma anon_none_grant : forall mo,
  negb (mmap_anon_b (Z_to_bv 64 flags)) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_reserve_refusable mo nZ = false ->
  exists eg mg, check_mmap (Z_to_bv 64 addr) lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo G2 G3 Hshape R. destruct anon_len_facts as [L0 L1].
  unfold mmap_reserve_refusable in R. apply negb_false_iff in R.
  destruct (vm_gap_available_find _ _ R) as [b Hfind].
  destruct (vm_find_base_sound _ _ _ Hfind) as (B1 & B2 & B3 & B4).
  pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
  assert (NB : errno_ret_in mmap_errnos b = false)
    by (apply errno_ret_in_mmap_small; apply (errno_of_below_top b (m_vmmaps mo) nZ); [lia | exact B3]).
  exists (mkEffectU b [] [] [(b, Z_to_bv 64 nZ)] [] []). eexists. split; [|exact NB].
  unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
  rewrite G2, L0, G3, Hshape. cbv iota beta. rewrite NB. cbv zeta. rewrite L1.
  rewrite (proj2 (Z.eqb_eq _ _) B1), (proj2 (Z.ltb_lt _ _) B2), (proj2 (Z.leb_le _ _) B3), B4.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hlen lenw"] Lemma nstep_mmap_rw_err_refusable : forall mo rsp mo' evs e,
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape H He. pose proof H as Hst. destruct anon_len_facts as [L0 L1].
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw in H.
  assert (G1 : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false) by reflexivity.
  assert (G2 : negb (mmap_anon_b (Z_to_bv 64 flags)) = false).
  { unfold mmap_modeled_b in Hshape. apply andb_prop in Hshape as [Hs _]. apply andb_prop in Hs as [_ Hs].
    unfold mmap_anon_b. apply Z.eqb_eq in Hs. unfold mmap_flags_core in Hs.
    apply negb_false_iff. apply negb_true_iff. apply Z.eqb_neq. intros Z0.
    assert (T : Z.testbit (Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE) 5 = true) by (rewrite Hs; reflexivity).
    rewrite Z.ldiff_spec in T. apply andb_prop in T as [T _].
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
    rewrite Z0 in T'. discriminate. }
  rewrite G1, G2, L0, Hshape in H. cbv iota beta in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  rewrite L1 in H. fold nZ in H.
  case_errno_in_eqn H Herr.
  - apply errno_ret_in_mmap_inv in Herr. subst r. destruct zs; [|discriminate]. injection H as <- <-.
    Local Ltac2 Set LiaHints.tbl := fun () => "0030>15920034181.1618758808802.2263233237716.2300000100700@SS4HlenS4Hlen2H0".
rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-. split; [reflexivity|]. split; [|auto].
    destruct (mmap_grant_refusable (Z_to_bv 64 flags) mo nZ) eqn:R; [reflexivity|]. exfalso.
    destruct (anon_rw_grant mo G2 Hshape R) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
    rewrite errno_ret_in_mmap_ENOMEM in X. discriminate X.
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [_ E].
    apply Z.leb_le in E. pose proof (mmap_len_bound len ltac:(lia)). fold nZ in H.
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) E) in He. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Hlen lenw"] Lemma nstep_mmap_none_err_refusable : forall mo rsp mo' evs e,
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ mmap_reserve_refusable mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape H He. pose proof H as Hst. destruct anon_len_facts as [L0 L1].
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw in H.
  assert (G1 : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false) by reflexivity.
  assert (Hs0 := Hshape). unfold mmap_noaccess_b in Hs0. apply andb_prop in Hs0 as [Hs0 _]. apply andb_prop in Hs0 as [Hp Hf].
  assert (G2 : negb (mmap_anon_b (Z_to_bv 64 flags)) = false).
  { unfold mmap_anon_b. apply Z.eqb_eq in Hf. unfold mmap_flags_core in Hf.
    apply negb_false_iff. apply negb_true_iff. apply Z.eqb_neq. intros Z0.
    assert (T : Z.testbit (Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE) 5 = true) by (rewrite Hf; reflexivity).
    rewrite Z.ldiff_spec in T. apply andb_prop in T as [T _].
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
    rewrite Z0 in T'. discriminate. }
  assert (G3 : mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false).
  { unfold mmap_modeled_b. apply Z.eqb_eq in Hp. rewrite Hp. reflexivity. }
  rewrite G1, G2, L0, G3, Hshape in H. cbv iota beta in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct ws; [|discriminate]. destruct zs; [|discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  rewrite L1 in H. fold nZ in H.
  case_errno_in_eqn H Herr.
  - apply errno_ret_in_mmap_inv in Herr. subst r. destruct us; [|discriminate]. injection H as <- <-.
    Local Ltac2 Set LiaHints.tbl := fun () => "0030>15920034306.1918758809445.2563233237716.2600000100700@SS4HlenS4Hlen2H0".
rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-. split; [reflexivity|]. split; [|auto].
    destruct (mmap_reserve_refusable mo nZ) eqn:R; [reflexivity|]. exfalso.
    destruct (anon_none_grant mo G2 G3 Hshape R) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
    rewrite errno_ret_in_mmap_ENOMEM in X. discriminate X.
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [_ E].
    apply Z.leb_le in E. pose proof (mmap_len_bound len ltac:(lia)). fold nZ in H.
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) E) in He. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End AnonMmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FixedMmap.
Variables (a len prot flags : Z).
Hypothesis Hlen : 0 < len < 2^64.
Hypothesis Ha : 0 <= a.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hwrap : a + mmap_len len < 2^64.

Let aw := Z_to_bv 64 a.
Let lenw := Z_to_bv 64 len.
Let nZ := mmap_len len.
Let nw := Z_to_bv 64 nZ.

#[using="Hlen Ha Hwrap"] Lemma fixed_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ /\ bv_unsigned aw = a.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>18758422825.122015597406.12 56759370246.1265127367338.1165127367338.1200000900B00S00\00eS4Hlen2HaS4Hlen2HaS4Hlen2Ha5Hwrap1HS4Hlen2HaS4Hlen2Ha".
pose proof (mmap_len_bound len ltac:(lia)).
  repeat split.
  - subst lenw. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - subst lenw nZ. rewrite unsigned_lit by lia. reflexivity.
  - subst aw. apply unsigned_lit. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Hlen Ha Hwrap nZ"] Lemma fixed_gate_wrap : (two_pow_64 <=? bv_unsigned aw + page_round_up_Z (bv_unsigned lenw)) = false.
Proof.
  destruct fixed_len_facts as (_ & -> & ->). apply Z.leb_gt. unfold two_pow_64. subst nZ. Local Ltac2 Set LiaHints.tbl := fun () => "0010=3163529770.1100000:S2Ha5Hwrap".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="len Hlen Ha Hal Hwrap lenw nZ"] Lemma fixed_gate_align : negb (Z.eqb (bv_unsigned aw mod page_size) 0) = false.
Proof. destruct fixed_len_facts as (_ & _ & ->). rewrite page_size_4096, Hal. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fixed_shape_pre :
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false
  /\ negb (mmap_anon_b (Z_to_bv 64 flags)) = false
  /\ mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false.
Proof.
  intros Hs.
  assert (CORE : mmap_flags_core (Z_to_bv 64 flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED
                 \/ mmap_flags_core (Z_to_bv 64 flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED_NOREPLACE
                 \/ mmap_flags_core (Z_to_bv 64 flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED + MAP_FIXED_NOREPLACE).
  { (* [comment removed for export] *)
    destruct (mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S1.
    { unfold mmap_fixed_noaccess_b in S1. apply andb_prop in S1 as [S1 _]. apply andb_prop in S1 as [_ Hc].
      apply Z.eqb_eq in Hc. auto. }
    destruct (mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S2.
    { unfold mmap_fixed_rw_b in S2. apply andb_prop in S2 as [S2 _]. apply andb_prop in S2 as [_ Hc].
      apply Z.eqb_eq in Hc. auto. }
    destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S3.
    { unfold mmap_noreplace_noaccess_b in S3. apply andb_prop in S3 as [S3 _]. apply andb_prop in S3 as [_ Hc].
      unfold mmap_noreplace_flags_b in Hc. apply orb_prop in Hc as [Hc|Hc]; apply Z.eqb_eq in Hc; auto. }
    destruct (mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S4.
    { unfold mmap_noreplace_rw_b in S4. apply andb_prop in S4 as [S4 _]. apply andb_prop in S4 as [_ Hc].
      unfold mmap_noreplace_flags_b in Hc. apply orb_prop in Hc as [Hc|Hc]; apply Z.eqb_eq in Hc; auto. }
    discriminate Hs. }
  assert (BIT : Z.testbit (mmap_flags_core (Z_to_bv 64 flags)) 5 = true)
    by (destruct CORE as [-> |[-> | ->]]; reflexivity).
  unfold mmap_flags_core in BIT. rewrite Z.ldiff_spec in BIT. apply andb_prop in BIT as [BIT _].
  split; [reflexivity|]. split.
  { unfold mmap_anon_b. apply negb_false_iff, negb_true_iff, Z.eqb_neq. intros Z0.
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, BIT; reflexivity).
    rewrite Z0 in T'. discriminate. }
  assert (NE : Z.eqb (mmap_flags_core (Z_to_bv 64 flags)) (MAP_PRIVATE + MAP_ANONYMOUS) = false)
    by (destruct CORE as [-> |[-> | ->]]; reflexivity).
  unfold mmap_modeled_b, mmap_noaccess_b. rewrite NE, !andb_false_r. auto.
Qed.

#[using="Hlen Ha Hal Hwrap lenw nZ nw"] Lemma fixed_none_grant : forall mo,
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  a + nZ <= alloc_top (m_vmmaps mo) -> negb (0 <? bv_unsigned aw) = false ->
  region_free (vm_reserved (m_vmmaps mo)) aw nw = true ->
  exists eg mg, check_mmap aw lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo Hshape Htop Hpos Hres. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape; reflexivity)) as (G1 & G2 & G3 & G4).
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NE : errno_ret_in mmap_errnos aw = false).
  { apply errno_ret_in_mmap_small. apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Htop]. }
  exists (mkEffectU aw [] [] [(aw, nw)] [] []).
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  2: destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  all: eexists; split; [|exact NE].
  all: unfold check_mmap; rewrite G1, G2, L0, G3, G4, Hshape; cbv iota beta zeta.
  all: rewrite fixed_gate_wrap, fixed_gate_align, Hpos, L1, La; rewrite (proj2 (Z.leb_le _ _) Htop).
  all: cbn [negb]; cbv iota; fold nw; rewrite S1; try rewrite S2; try rewrite Hres.
  all: cbv iota; rewrite NE, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hlen Ha Hal Hwrap lenw nZ nw"] Lemma nstep_mmap_fixed_none_no_err : forall mo rsp mo' evs,
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap a len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = None /\ eff_ret rsp = aw /\ evs = [].
Proof.
  intros mo rsp mo' evs Hshape H. pose proof H as Hst. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape; reflexivity)) as (G1 & G2 & G3 & G4).
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, Hshape in H. cbv iota beta in H. cbv zeta in H.
  rewrite fixed_gate_wrap in H.
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:Gt; [discriminate|].
  rewrite fixed_gate_align in H.
  destruct (negb (0 <? bv_unsigned aw)) eqn:Gp; [discriminate|].
  apply negb_false_iff, Z.leb_le in Gt. rewrite L1, La in Gt.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>17919609578.2718758809572.2700000<00ES4Hlen2Ha2LBS4Hlen2Ha".
pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Gt]).
  rewrite L1 in H. fold nw in H.
  assert (Hres : region_free (vm_reserved (m_vmmaps mo)) aw nw = true).
  { destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:R3; [reflexivity|]. exfalso.
    destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:R2;
      [rewrite (region_free_app_l _ _ _ _ R2) in R3; discriminate R3|].
    cbn [andb] in H. cbv iota in H. discriminate H. }
  destruct (fixed_none_grant mo Hshape Gt Gp Hres) as (eg & mg & Hg & Hng).
  pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in NE |- *.
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  2: destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  3: destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:S3; [|discriminate].
  all: destruct ws; [|discriminate]; destruct zs; [|discriminate];
       destruct cs; [|destruct us; discriminate]; destruct ci; [|destruct us; discriminate].
  all: rewrite NE in H; cbv iota in H.
  all: destruct (bv_eqb r aw && _) eqn:E; [|discriminate]; apply andb_prop in E as [E _]; apply bv_eqb_eq in E; subst r.
  all: injection H as _ <-; auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Ltac noreplace_gate H L1 La GT aw lenw mo :=
  cbv zeta in H; rewrite fixed_gate_wrap in H;
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:GT; [discriminate|];
  rewrite fixed_gate_align in H;
  destruct (negb (0 <? bv_unsigned aw)) eqn:?Gp; [discriminate|];
  apply negb_false_iff, Z.leb_le in GT; rewrite L1, La in GT; rewrite L1 in H.

#[using="Type"] Lemma noreplace_not_fixed :
  mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false.
Proof.
  intros Hshape.
  assert (CORE : Z.eqb (mmap_flags_core (Z_to_bv 64 flags)) (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED) = false).
  { assert (NR : mmap_noreplace_flags_b (Z_to_bv 64 flags) = true).
    { destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S3.
      - unfold mmap_noreplace_noaccess_b in S3. apply andb_prop in S3 as [S3 _]. apply andb_prop in S3 as [_ S3]. exact S3.
      - cbn [orb] in Hshape. unfold mmap_noreplace_rw_b in Hshape.
        apply andb_prop in Hshape as [Hs _]. apply andb_prop in Hs as [_ Hs]. exact Hs. }
    unfold mmap_noreplace_flags_b in NR. apply orb_prop in NR as [NR|NR]; apply Z.eqb_eq in NR; rewrite NR; reflexivity. }
  unfold mmap_fixed_noaccess_b, mmap_fixed_rw_b. rewrite CORE, !andb_false_r. auto.
Qed.

Lemma errno_ret_in_mmap_EEXIST : errno_ret_in mmap_errnos (errno_ret EEXIST) = false.
Proof.
  unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite orb_false_r.
  destruct (bv_eqb (errno_ret EEXIST) (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. apply (f_equal errno_of) in E.
  rewrite !errno_of_errno_ret in E by (unfold EEXIST, ENOMEM; lia). discriminate E.
Qed.

#[using="Hlen Ha Hal Hwrap lenw nZ nw"] Lemma noreplace_grant : forall mo,
  mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  a + nZ <= alloc_top (m_vmmaps mo) -> negb (0 <? bv_unsigned aw) = false ->
  (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
   region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw = true ->
   mmap_fixed_fresh_refusable (Z_to_bv 64 flags) mo nZ = false) ->
  exists eg mg, check_mmap aw lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo Hshape Htop Hpos Hfresh. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre
              ltac:(destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)),
                              (mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0));
                    rewrite ?orb_true_r, ?orb_false_r; first [reflexivity | discriminate Hshape]))
    as (G1 & G2 & G3 & G4).
  destruct (noreplace_not_fixed Hshape) as [G5 G6].
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NE : errno_ret_in mmap_errnos aw = false).
  { apply errno_ret_in_mmap_small. apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Htop]. }
  destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2;
    destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:SN;
    [ exists (mkEffectU aw [] [] [(aw, nw)] [] [])
    | exists (mkEffectU aw [] [(aw, nw)] [] [] [])
    | exists (mkEffectU (errno_ret EEXIST) [] [] [] [] [])
    | exists (mkEffectU (errno_ret EEXIST) [] [] [] [] []) ];
    eexists; (split; [| first [exact NE | exact errno_ret_in_mmap_EEXIST]]);
    unfold check_mmap; rewrite G1, G2, L0, G3, G4, G5, G6, SN; [| cbn [orb] in Hshape; rewrite Hshape | | cbn [orb] in Hshape; rewrite Hshape];
    cbv iota beta zeta;
    rewrite fixed_gate_wrap, fixed_gate_align, Hpos, L1, La; rewrite (proj2 (Z.leb_le _ _) Htop);
    cbn [negb]; cbv iota; fold nw; rewrite S2; cbv iota.
  - rewrite NE, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - pose proof (Hfresh eq_refl eq_refl) as R. unfold mmap_fixed_fresh_refusable in R. apply negb_false_iff in R.
    rewrite NE, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), R. reflexivity.
  - rewrite errno_ret_in_mmap_EEXIST, bv_eqb_refl. reflexivity.
  - rewrite errno_ret_in_mmap_EEXIST, bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hlen Ha Hal Hwrap lenw"] Lemma nstep_mmap_noreplace_err : forall mo rsp mo' evs e,
  mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap a len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  let h := m_vmmaps mo in
  mo' = mo /\ evs = []
  /\ ( (region_free (vm_reserved h ++ vm_maps h) aw nw = false /\ e = EEXIST)
     \/ (region_free (vm_reserved h ++ vm_maps h) aw nw = true /\ e = ENOMEM
         /\ mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true
         /\ mmap_fixed_fresh_refusable (Z_to_bv 64 flags) mo nZ = true)).
Proof.
  intros mo rsp mo' evs e Hshape H He. pose proof H as Hst. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre
              ltac:(destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)),
                              (mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0));
                    rewrite ?orb_true_r, ?orb_false_r; first [reflexivity | discriminate Hshape]))
    as (G1 & G2 & G3 & G4).
  destruct (noreplace_not_fixed Hshape) as [G5 G6].
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, G5, G6 in H. cbv iota beta in H.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>15905458981.3617919609578.3718758809318.295258704101.31 00000400@00I00MS2HaS4Hlen2Ha2LBS4Hlen2HaS2Ha".
pose proof (mmap_len_bound len ltac:(lia)) as LB.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:SN;
    [| cbn [orb] in Hshape; rewrite Hshape in H]; noreplace_gate H L1 La GT aw lenw mo; fold nw in H;
    (assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact GT]));
    destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  - (* [comment removed for export] *)
    exfalso. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (noreplace_grant mo ltac:(rewrite SN; reflexivity) GT ltac:(assumption)
                (fun Hn _ => ltac:(rewrite SN in Hn; discriminate Hn))) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE. cbn [eff_ret] in NE.
    rewrite NE in H. cbv iota in H.
    destruct (bv_eqb r aw) eqn:E; [| cbn [andb] in H; cbv iota in H; discriminate]. apply bv_eqb_eq in E. subst r. rewrite NOERR in He. discriminate.
  - (* [comment removed for export] *)
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (noreplace_grant mo ltac:(rewrite SN; reflexivity) GT ltac:(assumption)
                (fun _ Hr => ltac:(rewrite S2 in Hr; discriminate Hr))) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE. cbn [eff_ret] in NE.
    rewrite NE in H. cbn [orb] in H.
    destruct (bv_eqb r (errno_ret EEXIST)) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst r. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold EEXIST; lia). injection He as <-. repeat split; try reflexivity. left. auto.
  - (* [comment removed for export] *)
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    fold nZ in H. case_errno_in_eqn H Herr.
    + apply errno_ret_in_mmap_inv in Herr. subst r. rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
      destruct zs; [|discriminate]. injection H as <- <-. repeat split; try reflexivity. right.
      split; [exact S2|]. split; [reflexivity|]. split; [exact Hshape|].
      destruct (mmap_fixed_fresh_refusable (Z_to_bv 64 flags) mo nZ) eqn:R; [reflexivity|]. exfalso.
      destruct (noreplace_grant mo ltac:(rewrite SN; exact Hshape) GT ltac:(assumption) (fun _ _ => R))
        as (eg & mg & Hg & Hng).
      pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
      rewrite errno_ret_in_mmap_ENOMEM in X. discriminate X.
    + exfalso. destruct (bv_eqb r aw) eqn:E; [| cbn [andb] in H; cbv iota in H; discriminate].
      apply bv_eqb_eq in E. subst r. rewrite NOERR in He. discriminate.
  - (* [comment removed for export] *)
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (noreplace_grant mo ltac:(rewrite SN; exact Hshape) GT ltac:(assumption)
                (fun _ Hr => ltac:(rewrite S2 in Hr; discriminate Hr))) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE. cbn [eff_ret] in NE.
    rewrite NE in H. cbn [orb] in H.
    destruct (bv_eqb r (errno_ret EEXIST)) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst r. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold EEXIST; lia). injection He as <-. repeat split; try reflexivity. left. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FixedMmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Mprotect.
Variables (a len : Z).
Hypothesis Hlen : 0 < len < 2^64.
Hypothesis Ha : 0 <= a.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hwrap : a + mmap_len len < 2^64.

Let aw := Z_to_bv 64 a.
Let nZ := mmap_len len.
Let nw := Z_to_bv 64 nZ.

#[using="Hlen Ha Hal Hwrap"] Lemma mprotect_grant : forall mo,
  map_contains (vm_noaccess (m_vmmaps mo)) aw nw = true -> map_contains (vm_maps (m_vmmaps mo)) aw nw = true ->
  mprotect_refusable mo aw nw = false ->
  exists eg mg, check_mprotect aw (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE)) eg mo = CheckOk mg []
                /\ errno_ret_in mprotect_errnos (eff_ret eg) = false.
Proof.
  intros mo C1 C2 R. unfold mprotect_refusable in R. apply negb_false_iff in R.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (La : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Ll : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (N0 : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false)
    by (apply errno_ret_in_mprotect_small; apply errno_of_lit; lia).
  exists (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] []). eexists. split; [|exact N0].
  unfold check_mprotect.
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false.
  rewrite La, page_size_4096, Hal. cbn [Z.eqb negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Ll. fold (mmap_len len). fold nZ.
  replace (two_pow_64 <=? a + nZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; subst nZ; lia).
  change (negb (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)))) with false. cbv iota zeta. fold nw.
  rewrite C1, C2. cbn [andb]. cbv iota. rewrite N0, R. change (w_is0 (Z_to_bv 64 0)) with true.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

#[using="Hlen Ha Hal Hwrap"] Lemma nstep_mprotect_err_refusable : forall mo rsp mo' evs e,
  nstep (NMprotect a len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  let h := m_vmmaps mo in
  e = ENOMEM /\ mo' = mo /\ evs = []
  /\ map_contains (vm_noaccess h) aw nw = true /\ map_contains (vm_maps h) aw nw = true
  /\ mprotect_refusable mo aw nw = true.
Proof.
  intros mo rsp mo' evs e H He. Local Ltac2 Set LiaHints.tbl := fun () => "0090>15920176859.2218758983223.162017624378.19 3162974399.18 56765597452.1659020306144.1959020306144.2265121145038.1965121146689.1800000400=00F00P00b00f00j01301<S2HaS4Hlen2HaS4Hlen2HaS2Ha5HwrapS4Hlen2Ha5Hwrap2LBS2HaS2HaS4Hlen2HaS4Hlen2Ha".
pose proof (mmap_len_bound len ltac:(lia)) as LB.
  pose proof H as Hst. apply nstep_mprotect_iff in H as [H _]. unfold check_mprotect in H. fold aw in H.
  assert (La : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Ll : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
  rewrite La, page_size_4096, Hal in H. cbn [Z.eqb negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  rewrite Ll in H. fold (mmap_len len) in H. fold nZ in H.
  replace (two_pow_64 <=? a + nZ) with false in H by (symmetry; apply Z.leb_gt; unfold two_pow_64; subst nZ; lia).
  change (negb (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)))) with false in H. cbv iota zeta in H. fold nw in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct (map_contains (vm_noaccess (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  - apply andb_prop in S1 as [C1 C2].
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    case_errno_in_eqn H Herr.
    + apply errno_ret_in_mprotect_inv in Herr. subst r. rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
      destruct zs; [|discriminate]. injection H as <- <-. repeat split; auto.
      destruct (mprotect_refusable mo aw nw) eqn:R; [reflexivity|]. exfalso.
      destruct (mprotect_grant mo C1 C2 R) as (eg & mg & Hg & Hng).
      pose proof (nstep_mprotect_grant_no_errno _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
      rewrite errno_ret_in_mprotect_ENOMEM in X. discriminate X.
    + exfalso. destruct (mprotect_budget_ok mo aw nw && w_is0 r && _) eqn:E; [|discriminate].
      apply andb_prop in E as [E _]. apply andb_prop in E as [_ E]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
      rewrite errno_of_lit in He by lia. discriminate.
  - exfalso. destruct (map_contains (vm_maps (m_vmmaps mo)) aw nw && region_free (vm_noaccess (m_vmmaps mo)) aw nw); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    rewrite errno_of_lit in He by lia. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma mprotect_refusable_false_intro : forall mo,
  vm_backing_used (mprotect_model_next mo aw nw) <= vm_limit (m_vmmaps mo) ->
  mprotect_refusable mo aw nw = false.
Proof.
  intros mo Hb. unfold mprotect_refusable, mprotect_budget_ok, vm_backing_within_limit.
  unfold mprotect_model_next in *. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit].
  rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.
End Mprotect.
