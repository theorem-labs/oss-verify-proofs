(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ModelX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanTotalCore AsanInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg EdDefs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Bridge.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mmap_len_eq : forall len, 0 <= len < 2^63 -> page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = mmap_len len.
Proof. intros. unfold mmap_len. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma mmap_len_bounds : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. pose proof (Z.div_mod (l + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Section NodeSem.
Variable atop : Z.
Hypothesis Hatop : atop_ok atop.

Let atop_lt : atop < 2^47.
Proof. destruct Hatop as [_ H]. unfold ATOP_MAX in H. lia. Qed.

Let G_off : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false. Proof. reflexivity. Qed.
Let G_anon : forall flags, (flags = F_ANON \/ flags = F_FIXED \/ flags = F_FIXNORES) -> negb (mmap_anon_b (Z_to_bv 64 flags)) = false.
Proof. intros flags [-> |[-> | ->]]; reflexivity. Qed.

Lemma hint_nonspur : forall len mo rsp, 0 < len <= 2^40 ->
  (~ spurious_refusal_cfg fcfg
       (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 PROT_RW; Z_to_bv 64 F_ANON; Z_to_bv 64 (-1); Z_to_bv 64 0])
       mo rsp <->
   (bv_eqb (eff_ret rsp) (errno_ret ENOMEM) = true ->
    mmap_grant_refusable (Z_to_bv 64 F_ANON) mo (mmap_len len) = true)).
Proof.
  intros len mo rsp Hlen.
  assert (Hw : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  rewrite <- (mmap_len_eq len) by lia.
  set (i := pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 PROT_RW; Z_to_bv 64 F_ANON; Z_to_bv 64 (-1); Z_to_bv 64 0]).
  assert (E : bv_unsigned (in_sysno i) = 222) by reflexivity.
  rewrite <- (Bridge.refusal_b_222 i mo (eff_ret rsp) E).
  apply (Bridge.mmap_grant_nonspur i mo rsp E); [reflexivity | reflexivity | exact Hw | reflexivity].
Qed.

Lemma fixed_shape0 : forall flags, (flags = F_FIXED \/ flags = F_FIXNORES) ->
  mmap_anon_b (Z_to_bv 64 flags) = true.
Proof. intros flags [-> | ->]; reflexivity. Qed.

Lemma grant_answers : forall len mo rsp mo' evs,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs ->
  evs = [] /\ exists z, adec_mmap atop len PROT_RW rsp = Some z
   /\ z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
   /\ mo' = grant_model mo z (mmap_len len).
Proof.
  intros len mo rsp mo' evs Hlen Htop Hbud Hgap Hst.
  apply nstepA_mmap_iff in Hst as [Hst Hns]. unfold check_mmap in Hst.
  rewrite G_off, (G_anon F_ANON ltac:(auto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true in Hst.
  cbv iota beta in Hst. rewrite mmap_len_eq in Hst by lia.
  assert (Hnr : mmap_grant_refusable (Z_to_bv 64 F_ANON) mo (mmap_len len) = false).
  { unfold mmap_grant_refusable. rewrite Hgap. unfold mmap_noreserve_backed_ok.
    change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity. }
  generalize (proj1 (hint_nonspur len mo rsp Hlen) Hns); clear Hns; intros Hns. rewrite Hnr in Hns.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  cbn [eff_ret] in Hns. cbv beta iota zeta in Hst.
  replace (errno_ret_in mmap_errnos r) with false in Hst
    by (unfold errno_ret_in, mmap_errnos; cbn [existsb]; rewrite orb_false_r;
        destruct (bv_eqb r (errno_ret ENOMEM)); [discriminate (Hns eq_refl) | reflexivity]).
  cbv iota zeta in Hst.
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E Hzs]. apply andb_prop in E as [E Hb]. apply andb_prop in E as [E Hrf].
  apply andb_prop in E as [E Htp]. apply andb_prop in E as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htp. apply listNN_eqb_eq in Hzs.
  rewrite Htop in Htp. unfold page_size in Hal.
  subst zs. exists (bv_unsigned r).
  assert (Hr : Z_to_bv 64 (bv_unsigned r) = r) by apply Z_to_bv_bv_unsigned.
  rewrite Hr. split.
  - unfold adec_mmap. change (PROT_RW =? 0) with false. cbv iota. unfold dec_mmap.
    rewrite !bv_eqb_refl.
    replace (mmap_addr_ok atop len [] (bv_unsigned r)) with true; [reflexivity|].
    symmetry. unfold mmap_addr_ok. cbn [avoids forallb]. unfold page_size. rewrite Hal, (proj2 (Z.ltb_lt _ _) Hpos), (proj2 (Z.leb_le _ _) Htp). reflexivity.
  - split; [exact Hal|]. split; [exact Hpos|]. split; [exact Htp|]. split; [exact Hrf|].
    unfold grant_model, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota.
    rewrite Hr. reflexivity.
Qed.

Lemma grant_exists : forall len mo,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  exists rsp mo' evs, nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs.
Proof.
  intros len mo Hlen Htop Hbud Hgap.
  destruct (vm_gap_available_find _ _ Hgap) as [a Hf].
  pose proof (vm_find_base_sound _ _ _ Hf) as (A1 & A2 & A3 & A4).
  eexists (mkEffectU a [] [(a, Z_to_bv 64 (mmap_len len))] [] [] []), _, [].
  apply nstepA_mmap_iff. split.
  2:{ apply fcfg_nonref_nonspur. apply (Bridge.refusal_b_222_placed _ mo _ (m_vmmaps mo) (mmap_len len));
      [reflexivity | pose proof (mmap_len_bounds len ltac:(lia)); lia | exact A3]. }
  unfold check_mmap.
  rewrite G_off, (G_anon F_ANON ltac:(auto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true.
  cbv iota beta. rewrite mmap_len_eq by lia.
  assert (Hne : errno_ret_in mmap_errnos a = false).
  { unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite orb_false_r. apply Bridge.bv_eqb_enomem_below.
    pose proof (mmap_len_bounds len ltac:(lia)). pose proof atop_lt. rewrite Htop in A3. unfold two_pow_64. lia. }
  rewrite Hne. cbv iota zeta.
  rewrite A1, (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3), A4.
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud).
  cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma fixed_shape : forall flags, (flags = F_FIXED \/ flags = F_FIXNORES) ->
  mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true.
Proof. intros flags [-> | ->]; repeat split; reflexivity. Qed.

Lemma fixed_nonspur : forall addr len flags mo rsp,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  alloc_top (m_vmmaps mo) = atop -> addr + mmap_len len <= atop ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true ->
  (~ spurious_refusal_cfg fcfg
       (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 PROT_RW; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
       mo rsp <->
   (bv_eqb (eff_ret rsp) (errno_ret ENOMEM) = true ->
    mmap_fixed_commit_refusable (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true)).
Proof.
  intros addr len flags mo rsp Hfl Hlen Ha Hal Htop Hce Hrf Hmc.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof atop_lt.
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4).
  assert (Hw : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (A0 : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; lia).
  rewrite <- (mmap_len_eq len) in Hrf, Hmc |- * by lia.
  set (i := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 PROT_RW; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]).
  assert (E : bv_unsigned (in_sysno i) = 222) by reflexivity.
  rewrite <- (Bridge.refusal_b_222 i mo (eff_ret rsp) E).
  apply (Bridge.mmap_fixed_commit_nonspur i mo rsp E);
    [reflexivity | exact (fixed_shape0 flags Hfl) | exact Hw | exact S1 | exact S2 | exact S3 | exact S4
    | | | | exact Hrf | exact Hmc].
  - change (in_arg i 0) with (Z_to_bv 64 addr). change (in_arg i 1) with (Z_to_bv 64 len).
    rewrite A0, mmap_len_eq by lia. rewrite Htop. exact Hce.
  - change (in_arg i 0) with (Z_to_bv 64 addr). rewrite A0. exact Hal.
  - change (in_arg i 0) with (Z_to_bv 64 addr). rewrite A0. exact Ha.
Qed.

Lemma fixed_answers : forall addr len flags mo rsp mo' evs,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  alloc_top (m_vmmaps mo) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  nstepA (NMmap addr len PROT_RW flags) mo rsp mo' evs ->
  evs = [] /\ adec_mmap atop len PROT_RW rsp = Some addr
  /\ mo' = with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) n) mo).
Proof.
  intros addr len flags mo rsp mo' evs Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud Hst.
  apply nstepA_mmap_iff in Hst as [Hst Hns]. unfold check_mmap in Hst.
  rewrite G_off, (G_anon flags ltac:(tauto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4 in Hst. cbv iota beta in Hst.
  rewrite mmap_len_eq in Hst by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) in Hst by lia.
  cbv zeta in Hst.
  replace (two_pow_64 <=? addr + mmap_len len) with false in Hst by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce) in Hst. unfold page_size in Hst. rewrite Hal in Hst. rewrite (proj2 (Z.ltb_lt _ _) Ha) in Hst.
  cbn [negb Z.eqb] in Hst. fold n in Hst. rewrite Hrf, Hmc in Hst. cbn [andb] in Hst.
  assert (Hnr : mmap_fixed_commit_refusable (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = false).
  { unfold mmap_fixed_commit_refusable. rewrite Hbud. reflexivity. }
  generalize (proj1 (fixed_nonspur addr len flags mo rsp Hfl Hlen Ha Hal Htop Hce Hrf Hmc) Hns); clear Hns; intros Hns.
  fold n in Hns. rewrite Hnr in Hns.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  cbn [eff_ret] in Hns. cbv beta iota zeta in Hst.
  replace (errno_ret_in mmap_errnos r) with false in Hst
    by (unfold errno_ret_in, mmap_errnos; cbn [existsb]; rewrite orb_false_r;
        destruct (bv_eqb r (errno_ret ENOMEM)); [discriminate (Hns eq_refl) | reflexivity]).
  cbv iota in Hst.
  destruct us; [|discriminate]. cbv iota in Hst.
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r zs.
  split; [|reflexivity].
  unfold adec_mmap. change (PROT_RW =? 0) with false. cbv iota. unfold dec_mmap. fold n. rewrite !bv_eqb_refl.
  rewrite unsigned_lit by lia.
  replace (mmap_addr_ok atop len [] addr) with true; [reflexivity|].
  symmetry. unfold mmap_addr_ok. cbn [avoids forallb]. unfold page_size. rewrite Hal, (proj2 (Z.ltb_lt _ _) Ha), (proj2 (Z.leb_le _ _) Hce). reflexivity.
Qed.

Lemma fixed_exists : forall addr len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  alloc_top (m_vmmaps mo) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMmap addr len PROT_RW flags) mo rsp mo' evs.
Proof.
  intros addr len flags mo Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud.
  eexists (mkEffectU (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)] [] [] []), _, [].
  apply nstepA_mmap_iff. split.
  2:{ apply fcfg_nonref_nonspur. pose proof (mmap_len_bounds len ltac:(lia)).
      apply (Bridge.refusal_b_222_placed _ mo _ (m_vmmaps mo) (mmap_len len));
      [reflexivity | lia | cbn [eff_ret]; rewrite unsigned_lit by lia; rewrite Htop; lia]. }
  unfold check_mmap.
  rewrite G_off, (G_anon flags ltac:(tauto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4. cbv iota beta.
  rewrite mmap_len_eq by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) by lia.
  cbv zeta.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce). unfold page_size. rewrite Hal. rewrite (proj2 (Z.ltb_lt _ _) Ha).
  cbn [negb Z.eqb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  replace (errno_ret_in mmap_errnos (Z_to_bv 64 addr)) with false
    by (symmetry; unfold errno_ret_in, mmap_errnos; cbn [existsb]; rewrite orb_false_r; apply Bridge.bv_eqb_enomem_below;
        rewrite unsigned_lit by lia; pose proof atop_lt; unfold two_pow_64; lia).
  cbv iota. rewrite !bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hbud. reflexivity.
Qed.

Lemma munmap_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  nstepA (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ adec_munmap addr len rsp = Some 0
  /\ mo' = munmap_model mo addr (mmap_len len).
Proof.
  intros addr len mo rsp mo' evs Hlen Ha Hal Hce n Hmh Hst.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  cbn [nstepA] in Hst. apply nstep_munmap_iff in Hst. unfold check_munmap in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb] in Hst.
  rewrite mmap_len_eq in Hst by lia. cbv zeta in Hst.
  replace (TASK_SIZE <? addr + mmap_len len) with false in Hst by (symmetry; apply Z.ltb_ge; lia).
  fold n in Hst. rewrite Hmh in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E1 E2]. unfold w_is0 in E1. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r us.
  split.
  - unfold adec_munmap, dec_munmap. rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. fold n. rewrite !bv_eqb_refl. reflexivity.
  - unfold munmap_model. fold n. subst n. rewrite (unsigned_lit (mmap_len len)) by lia. reflexivity.
Qed.

Lemma munmap_exists : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hmh.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  eexists (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, n)] [] []), _, [].
  cbn [nstepA]. apply nstep_munmap_iff. unfold check_munmap.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
  rewrite mmap_len_eq by lia. cbv zeta.
  replace (TASK_SIZE <? addr + mmap_len len) with false by (symmetry; apply Z.ltb_ge; lia).
  fold n. rewrite Hmh. rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma grantT_answers : forall len mo rsp mo' evs,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs ->
  evs = [] /\ exists z, adec_mmap_tol atop len rsp = Some z /\
   ((z = TWO64 - 12 /\ mo' = mo /\ vm_gap_available (m_vmmaps mo) (mmap_len len) = false)
    \/ (z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
        /\ mo' = grant_model mo z (mmap_len len))).
Proof.
  intros len mo rsp mo' evs Hlen Htop Hbud Hst.
  destruct (vm_gap_available (m_vmmaps mo) (mmap_len len)) eqn:Hgap.
  { destruct (grant_answers len mo rsp mo' evs Hlen Htop Hbud Hgap Hst) as (-> & z & Hd & H1 & H2 & H3 & H4 & ->).
    split; [reflexivity|]. exists z. split; [| right; repeat split; auto].
    unfold adec_mmap in Hd. change (PROT_RW =? 0) with false in Hd. cbv iota in Hd. unfold adec_mmap_tol.
    destruct (dec_mmap atop len [] rsp) as [[e|x]|]; try discriminate Hd. exact Hd. }
  apply nstepA_mmap_iff in Hst as [Hst _]. unfold check_mmap in Hst.
  rewrite G_off, (G_anon F_ANON ltac:(auto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true in Hst.
  cbv iota beta in Hst. rewrite mmap_len_eq in Hst by lia.
  change mmap_errnos with [ENOMEM] in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  destruct (errno_ret_in [ENOMEM] r) eqn:ER.
  - destruct zs; [|discriminate]. injection Hst as <- <-. split; [reflexivity|].
    apply errno_ret_in_true in ER as (e & [<-|[]] & ->).
    exists (TWO64 - 12). split; [| left; split; [reflexivity| split; reflexivity]].
    unfold adec_mmap_tol, dec_mmap. rewrite (errno_of_errno_ret ENOMEM) by (unfold ENOMEM; lia). reflexivity.
  -
    exfalso. cbv zeta in Hst.
    match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E Hrf].
    apply andb_prop in E as [E Htp]. apply andb_prop in E as [Hal Hpos].
    assert (BOK : vm_base_ok (m_vmmaps mo) (mmap_len len) r = true).
    { unfold vm_base_ok. rewrite Hal, Hpos, Htp, Hrf. reflexivity. }
    rewrite (vm_find_base_complete _ _ _ BOK) in Hgap. discriminate Hgap.
Qed.

Lemma grantT_exists : forall len mo,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  exists rsp mo' evs, nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs.
Proof.
  intros len mo Hlen Htop Hbud.
  destruct (vm_gap_available (m_vmmaps mo) (mmap_len len)) eqn:Hgap; [exact (grant_exists len mo Hlen Htop Hbud Hgap)|].
  eexists (mkEffectU (errno_ret ENOMEM) [] [] [] [] []), _, [].
  apply nstepA_mmap_iff. split.
  2:{ apply (proj2 (hint_nonspur len mo _ Hlen)). intros _. unfold mmap_grant_refusable. rewrite Hgap. apply orb_true_r. }
  unfold check_mmap.
  rewrite G_off, (G_anon F_ANON ltac:(auto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true.
  cbv iota beta. rewrite mmap_len_eq by lia.
  change mmap_errnos with [ENOMEM]. cbn [errno_ret_in existsb]. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma canon_madvise_next : forall mo (a n : word), m_vm_materialized mo = [] -> madvise_dontneed_next mo a n = mo.
Proof.
  intros mo a n H. unfold madvise_dontneed_next. rewrite H. cbn [List.filter].
  rewrite <- H. exact (ModelX.MX_mat mo).
Qed.

Lemma madvise_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> len mod 4096 = 0 -> 0 <= addr -> addr mod 4096 = 0 -> addr + len < 2^64 ->
  m_vm_materialized mo = [] ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 len) = true ->
  nstepA (NMadvise addr len) mo rsp mo' evs ->
  evs = [] /\ adec_madvise addr len rsp = Some 0 /\ mo' = mo.
Proof.
  intros addr len mo rsp mo' evs Hlen Hl4 Ha Hal Hhi Hcan Hok Hst.
  cbn [nstepA] in Hst. apply nstep_madvise_iff in Hst. unfold check_madvise in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst. cbn [Z.eqb negb] in Hst.
  change (madvise_dontneed_b (Z_to_bv 64 4)) with true in Hst. cbn [negb] in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  assert (ML : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = len).
  { rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size. pose proof (Z.div_mod len 4096 ltac:(lia)).
    replace (len + 4096 - 1) with ((len / 4096) * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  rewrite ML in Hst. unfold two_pow_64 in Hst. replace (2 ^ 64 <=? addr + len) with false in Hst by (symmetry; apply Z.leb_gt; lia).
  cbv zeta in Hst. rewrite Hok in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. apply andb_prop in E as [R0 ZS]. apply listNN_eqb_eq in ZS. subst zs.
  split; [reflexivity|]. split; [| apply canon_madvise_next; exact Hcan].
  unfold adec_madvise. unfold w_is0 in R0. apply Z.eqb_eq in R0. rewrite R0. rewrite !unsigned_lit by lia. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma madvise_exists : forall addr len mo,
  0 < len <= 2^40 -> len mod 4096 = 0 -> 0 <= addr -> addr mod 4096 = 0 -> addr + len < 2^64 ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 len) = true ->
  exists rsp mo' evs, nstepA (NMadvise addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Hl4 Ha Hal Hhi Hok.
  eexists (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 len)] [] [] []), _, [].
  cbn [nstepA]. apply nstep_madvise_iff. unfold check_madvise.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal. cbn [Z.eqb negb].
  change (madvise_dontneed_b (Z_to_bv 64 4)) with true. cbn [negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (ML : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = len).
  { rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size. pose proof (Z.div_mod len 4096 ltac:(lia)).
    replace (len + 4096 - 1) with ((len / 4096) * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  rewrite ML. unfold two_pow_64. replace (2 ^ 64 <=? addr + len) with false by (symmetry; apply Z.leb_gt; lia).
  cbv zeta. rewrite Hok. rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Definition aok (e : aev) (mo : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      prot = PROT_RW /\ 0 < len <= 2^40 /\ alloc_top (m_vmmaps mo) = atop /\
      if addr =? 0 then
        flags = F_ANON /\ vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo)
        /\ vm_gap_available (m_vmmaps mo) (mmap_len len) = true
      else
        (flags = F_FIXED \/ flags = F_FIXNORES) /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | AMunmap addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
      /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | AMmapT len =>
      0 < len <= 2^40 /\ alloc_top (m_vmmaps mo) = atop /\ vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo)
  | AMadvise addr len =>
      0 < len <= 2^40 /\ len mod 4096 = 0 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + len < 2^64
      /\ m_vm_materialized mo = []
      /\ madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 len) = true
  | _ => False
  end.

Definition apost (e : aev) (mo : Model) (z : Z) (mo' : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      if addr =? 0 then
        z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
        /\ mo' = grant_model mo z (mmap_len len)
      else z = addr /\ mo' = fixed_model mo flags addr (mmap_len len)
  | AMunmap addr len => z = 0 /\ mo' = munmap_model mo addr (mmap_len len)
  | AMmapT len =>
      (z = TWO64 - 12 /\ mo' = mo /\ vm_gap_available (m_vmmaps mo) (mmap_len len) = false)
      \/ (z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
          /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
          /\ mo' = grant_model mo z (mmap_len len))
  | AMadvise addr len => z = 0 /\ mo' = mo
  | _ => False
  end.

Theorem asan_node_sound : node_sound atop nstepA aok apost.
Proof.
  intros e mo Hok. destruct e as [t|b|addr len prot flags|addr len|a l p|addr len|len|w]; try (destruct Hok; fail); try contradiction.
  -
    cbn [aok] in Hok. destruct Hok as (-> & Hlen & Htop & Hc).
    exists (NMmap addr len PROT_RW flags), (adec_mmap atop len PROT_RW). split; [reflexivity|].
    destruct (Z.eqb_spec addr 0) as [->|Hnz].
    + destruct Hc as (-> & Hbud & Hgap). split; [|split].
      * intros rsp mo' evs Hst. destruct (grant_answers len mo rsp mo' evs Hlen Htop Hbud Hgap Hst) as (-> & z & Hd & H1 & H2 & H3 & H4 & ->).
        split; [reflexivity|]. exists z. split; [exact Hd|]. cbn [apost]. rewrite Z.eqb_refl. repeat split; auto.
      * apply grant_exists; auto.
      * intros code mo' Hx. exact Hx.
    + destruct Hc as (Hfl & Ha & Hal & Hce & Hrf & Hmc & Hbud). split; [|split].
      * intros rsp mo' evs Hst. destruct (fixed_answers addr len flags mo rsp mo' evs Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud Hst) as (-> & Hd & ->).
        split; [reflexivity|]. exists addr. split; [exact Hd|]. cbn [apost]. replace (addr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; reflexivity.
      * apply (fixed_exists addr len flags mo); auto.
      * intros code mo' Hx. exact Hx.
  -
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hmh).
    exists (NMunmap addr len), (adec_munmap addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (munmap_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hmh Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (munmap_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
  -
    cbn [aok] in Hok. destruct Hok as (Hlen & Hl4 & Ha & Hal & Hhi & Hcan & Hmd).
    exists (NMadvise addr len), (adec_madvise addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (madvise_answers addr len mo rsp mo' evs Hlen Hl4 Ha Hal Hhi Hcan Hmd Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (madvise_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
  -
    cbn [aok] in Hok. destruct Hok as (Hlen & Htop & Hbud).
    exists (NMmap 0 len PROT_RW F_ANON), (adec_mmap_tol atop len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (grantT_answers len mo rsp mo' evs Hlen Htop Hbud Hst) as (-> & z & Hd & HP).
      split; [reflexivity|]. exists z. split; [exact Hd|]. cbn [apost]. exact HP.
    + apply grantT_exists; auto.
    + intros code mo' Hx. exact Hx.
Qed.

End NodeSem.
