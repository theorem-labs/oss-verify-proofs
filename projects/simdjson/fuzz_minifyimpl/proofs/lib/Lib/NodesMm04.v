(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Cfg MmEd NodesEd.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import MmapComplete.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  rewrite errno_of_errno_ret in Hn by lia. discriminate.
Qed.

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
  apply errno_of_small. lia.
Qed.

(* [comment removed for export] *)
Lemma bv_eqb_errno_small : forall e (aw : word), errno_of aw = None -> 1 <= e <= 4095 ->
  bv_eqb (errno_ret e) aw = false.
Proof.
  intros e aw Hn He. destruct (bv_eqb (errno_ret e) aw) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. rewrite <- E, errno_of_errno_ret in Hn by lia. discriminate.
Qed.

Lemma page_round_up_Z_nonneg' : forall z, 0 <= z -> 0 <= page_round_up_Z z.
Proof. intros z Hz. unfold page_round_up_Z, page_size. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]. Qed.

Lemma page_size_4096 : page_size = 4096.
Proof. reflexivity. Qed.

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
  assert (Hg : bv_unsigned (Z_to_bv 64 g) = g) by (apply unsigned_lit; lia).
  apply (MmapComplete.vm_gap_available_complete h nZ (Z_to_bv 64 g)); rewrite ?Hg; assumption.
Qed.

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

Lemma anon_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ.
Proof.
  split.
  - subst lenw. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - subst lenw nZ. rewrite unsigned_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_rw_err_refusable : forall mo rsp mo' evs e,
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape H He. destruct anon_len_facts as [L0 L1].
  apply nstep_mmap_ed in H as [_ H]; [| apply mmap_corner_free_not_rw, modeled_not_fixed_rw; exact Hshape].
  unfold check_mmap_ed in H. fold lenw in H.
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
  - apply errno_ret_in_when in Herr as [Hr ->]. destruct zs; [|discriminate]. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-. auto.
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [_ E].
    apply Z.leb_le in E. pose proof (mmap_len_bound len ltac:(lia)). fold nZ in H.
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) E) in He. discriminate.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_none_err_refusable : forall mo rsp mo' evs e,
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ mmap_reserve_refusable mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape H He. destruct anon_len_facts as [L0 L1].
  apply nstep_mmap_ed in H as [_ H]; [| apply mmap_corner_free_not_rw, noaccess_not_fixed_rw; exact Hshape].
  unfold check_mmap_ed in H. fold lenw in H.
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
  - apply errno_ret_in_when in Herr as [Hr ->]. destruct us; [|discriminate]. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-. auto.
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [_ E].
    apply Z.leb_le in E. pose proof (mmap_len_bound len ltac:(lia)). fold nZ in H.
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) E) in He. discriminate.
Qed.
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

Lemma fixed_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ /\ bv_unsigned aw = a.
Proof.
  pose proof (mmap_len_bound len ltac:(lia)).
  repeat split.
  - subst lenw. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - subst lenw nZ. rewrite unsigned_lit by lia. reflexivity.
  - subst aw. apply unsigned_lit. lia.
Qed.

(* [comment removed for export] *)
Lemma fixed_gate_wrap : (two_pow_64 <=? bv_unsigned aw + page_round_up_Z (bv_unsigned lenw)) = false.
Proof.
  destruct fixed_len_facts as (_ & -> & ->). apply Z.leb_gt. unfold two_pow_64. subst nZ. lia.
Qed.
Lemma fixed_gate_align : negb (Z.eqb (bv_unsigned aw mod page_size) 0) = false.
Proof. destruct fixed_len_facts as (_ & _ & ->). rewrite page_size_4096, Hal. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fixed_shape_pre :
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

(* [comment removed for export] *)
Lemma nstep_mmap_fixed_none_no_err : forall mo rsp mo' evs,
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap a len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = None /\ eff_ret rsp = aw /\ evs = [].
Proof.
  intros mo rsp mo' evs Hshape H. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape; reflexivity)) as (G1 & G2 & G3 & G4).
  apply nstep_mmap_ed in H as [_ H]; [| apply mmap_corner_free_not_rw, fixed_noaccess_not_fixed_rw; exact Hshape].
  unfold check_mmap_ed in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, Hshape in H. cbv iota beta in H. cbv zeta in H.
  rewrite fixed_gate_wrap in H.
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:Gt; [discriminate|].
  rewrite fixed_gate_align in H.
  destruct (negb (0 <? bv_unsigned aw)) eqn:Gp; [discriminate|].
  apply negb_false_iff, Z.leb_le in Gt. rewrite L1, La in Gt.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Gt]).
  rewrite L1 in H. fold nw in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret].
  rewrite mmap_errnos_when_false, mmap_destructive_errnos_nil in H.
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  2: destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  3: destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:S3; [|discriminate].
  all: destruct ws; [|discriminate]; destruct zs; [|discriminate];
       destruct cs; [|destruct us; discriminate]; destruct ci; [|destruct us; discriminate].
  all: rewrite !errno_ret_in_nil in H; cbn [andb] in H; cbv iota in H.
  all: destruct (bv_eqb r aw && _) eqn:E; [|discriminate]; apply andb_prop in E as [E _]; apply bv_eqb_eq in E; subst r.
  all: injection H as _ <-; auto.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_fixed_rw_err_refusable : forall mo rsp mo' evs e,
  mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap a len prot flags) mo rsp mo' evs ->
  mmap_corner_free aw lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) mo rsp ->
  errno_of (eff_ret rsp) = Some e ->
  let h := m_vmmaps mo in
  e = ENOMEM /\ mo' = mo /\ evs = []
  /\ ( (region_free (vm_reserved h) aw nw && map_contains (vm_maps h) aw nw = true
        /\ mmap_fixed_commit_refusable (Z_to_bv 64 flags) mo aw nw = true)
     \/ (region_free (vm_reserved h) aw nw && map_contains (vm_maps h) aw nw = false
        /\ region_free (vm_reserved h ++ vm_maps h) aw nw = true
        /\ mmap_fixed_fresh_refusable (Z_to_bv 64 flags) mo nZ = true)
     \/ (region_free (vm_reserved h) aw nw && map_contains (vm_maps h) aw nw = false
        /\ region_free (vm_reserved h ++ vm_maps h) aw nw = false
        /\ region_free (vm_reserved h) aw nw = true
        /\ mmap_fixed_span_refusable (Z_to_bv 64 flags) mo aw nw = true)).
Proof.
  intros mo rsp mo' evs e Hshape H Hcf He. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape, ?orb_true_r; reflexivity)) as (G1 & G2 & G3 & G4).
  assert (G5 : mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false).
  { unfold mmap_fixed_rw_b in Hshape. unfold mmap_fixed_noaccess_b. apply andb_prop in Hshape as [Hs _]. apply andb_prop in Hs as [Hp _].
    apply Z.eqb_eq in Hp. rewrite Hp. reflexivity. }
  apply nstep_mmap_ed in H as [_ H]; [|exact Hcf]. unfold check_mmap_ed in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, G5, Hshape in H. cbv iota beta in H. cbv zeta in H.
  rewrite fixed_gate_wrap in H.
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:Gt; [discriminate|].
  rewrite fixed_gate_align in H.
  destruct (negb (0 <? bv_unsigned aw)) eqn:Gp; [discriminate|].
  apply negb_false_iff, Z.leb_le in Gt. rewrite L1, La in Gt.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Gt]).
  rewrite L1 in H. fold nw in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  rewrite mmap_destructive_errnos_nil in H.
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  2: destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  3: destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:S3; [|discriminate].
  all: destruct ws; [|discriminate]; destruct cs; [|destruct zs, us; discriminate]; destruct ci; [|destruct zs, us; discriminate].
  all: rewrite ?errno_ret_in_nil in H.
  all: case_errno_in_eqn H Herr;
    [ apply errno_ret_in_when in Herr as [Hr ->];
      rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia); injection He as <-;
      rewrite ?(bv_eqb_errno_small ENOMEM aw NOERR ltac:(unfold ENOMEM; lia)) in H;
      destruct zs, us; cbn [w_nilb andb] in H; cbv iota in H; try discriminate H;
      injection H as <- <-; repeat split; try reflexivity
    | exfalso; cbn [andb] in H; cbv iota in H;
      first [ destruct us; [discriminate|] | idtac ];
      destruct (bv_eqb r aw) eqn:E; [| cbn [andb] in H; cbv iota in H; destruct us; discriminate];
      apply bv_eqb_eq in E; subst r; rewrite NOERR in He; discriminate ].
  - left. split; [exact S1| exact Hr].
  - right. left. split; [exact S1|]. split; [exact S2| exact Hr].
  - right. right. rewrite S3. split; [exact S1|]. split; [exact S2|]. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
Ltac noreplace_gate H L1 La GT aw lenw mo :=
  cbv zeta in H; rewrite fixed_gate_wrap in H;
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:GT; [discriminate|];
  rewrite fixed_gate_align in H;
  destruct (negb (0 <? bv_unsigned aw)) eqn:?Gp; [discriminate|];
  apply negb_false_iff, Z.leb_le in GT; rewrite L1, La in GT; rewrite L1 in H.

(* [comment removed for export] *)
Lemma nstep_mmap_noreplace_err : forall mo rsp mo' evs e,
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
  intros mo rsp mo' evs e Hshape H He. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre
              ltac:(destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)),
                              (mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0));
                    rewrite ?orb_true_r, ?orb_false_r; first [reflexivity | discriminate Hshape]))
    as (G1 & G2 & G3 & G4).
  assert (G56 : mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
                /\ mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false).
  { assert (CORE : Z.eqb (mmap_flags_core (Z_to_bv 64 flags)) (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED) = false).
    { assert (NR : mmap_noreplace_flags_b (Z_to_bv 64 flags) = true).
      { destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S3.
        - unfold mmap_noreplace_noaccess_b in S3. apply andb_prop in S3 as [S3 _]. apply andb_prop in S3 as [_ S3]. exact S3.
        - cbn [orb] in Hshape. unfold mmap_noreplace_rw_b in Hshape.
          apply andb_prop in Hshape as [Hs _]. apply andb_prop in Hs as [_ Hs]. exact Hs. }
      unfold mmap_noreplace_flags_b in NR. apply orb_prop in NR as [NR|NR]; apply Z.eqb_eq in NR; rewrite NR; reflexivity. }
    unfold mmap_fixed_noaccess_b, mmap_fixed_rw_b. rewrite CORE, !andb_false_r. auto. }
  destruct G56 as [G5 G6].
  apply nstep_mmap_ed in H as [_ H]; [| apply mmap_corner_free_not_rw; exact G6].
  unfold check_mmap_ed in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, G5, G6 in H. cbv iota beta in H.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:SN;
    [| cbn [orb] in Hshape; rewrite Hshape in H]; noreplace_gate H L1 La GT aw lenw mo; fold nw in H;
    (assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact GT]));
    rewrite mmap_errnos_when_false in H;
    destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  - (* [comment removed for export] *)
    exfalso. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    rewrite errno_ret_in_nil in H. cbv iota in H.
    destruct (bv_eqb r aw) eqn:E; [| cbn [andb] in H; cbv iota in H; discriminate]. apply bv_eqb_eq in E. subst r. rewrite NOERR in He. discriminate.
  - (* [comment removed for export] *)
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    rewrite errno_ret_in_nil in H. cbn [orb] in H.
    destruct (bv_eqb r (errno_ret EEXIST)) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst r. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold EEXIST; lia). injection He as <-. repeat split; try reflexivity. left. auto.
  - (* [comment removed for export] *)
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    fold nZ in H. case_errno_in_eqn H Herr.
    + apply errno_ret_in_when in Herr as [Hr ->]. rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
      destruct zs; [|discriminate]. injection H as <- <-. repeat split; try reflexivity. right. auto.
    + exfalso. destruct (bv_eqb r aw) eqn:E; [| cbn [andb] in H; cbv iota in H; discriminate].
      apply bv_eqb_eq in E. subst r. rewrite NOERR in He. discriminate.
  - (* [comment removed for export] *)
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    rewrite errno_ret_in_nil in H. cbn [orb] in H.
    destruct (bv_eqb r (errno_ret EEXIST)) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst r. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold EEXIST; lia). injection He as <-. repeat split; try reflexivity. left. auto.
Qed.
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

Lemma nstep_mprotect_err_refusable : forall mo rsp mo' evs e,
  nstep (NMprotect a len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  let h := m_vmmaps mo in
  e = ENOMEM /\ mo' = mo /\ evs = []
  /\ map_contains (vm_noaccess h) aw nw = true /\ map_contains (vm_maps h) aw nw = true
  /\ mprotect_refusable mo aw nw = true.
Proof.
  intros mo rsp mo' evs e H He. pose proof (mmap_len_bound len ltac:(lia)) as LB.
  apply nstep_mprotect_ed in H. unfold check_mprotect_ed in H. fold aw in H.
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
    + apply errno_ret_in_mprotect_when in Herr as [Hr ->]. rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
      destruct zs; [|discriminate]. injection H as <- <-. repeat split; auto.
    + exfalso. destruct (mprotect_budget_ok mo aw nw && w_is0 r && _) eqn:E; [|discriminate].
      apply andb_prop in E as [E _]. apply andb_prop in E as [_ E]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
      rewrite errno_of_lit in He by lia. discriminate.
  - exfalso. destruct (map_contains (vm_maps (m_vmmaps mo)) aw nw && region_free (vm_noaccess (m_vmmaps mo)) aw nw); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    rewrite errno_of_lit in He by lia. discriminate.
Qed.

(* [comment removed for export] *)
Lemma mprotect_refusable_false_intro : forall mo,
  vm_backing_used (mprotect_model_next mo aw nw) <= vm_limit (m_vmmaps mo) ->
  mprotect_refusable mo aw nw = false.
Proof.
  intros mo Hb. unfold mprotect_refusable, mprotect_budget_ok, vm_backing_within_limit.
  unfold mprotect_model_next in *. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit].
  rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.
End Mprotect.
