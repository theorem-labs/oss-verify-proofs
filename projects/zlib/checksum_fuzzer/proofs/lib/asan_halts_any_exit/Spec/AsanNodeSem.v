(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.FO.P04 Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import NodesA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree AsanCtrl AsanEmbed Monad RSim AsanProgDeps AsanTotalCore AsanInv.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* port727 candidate (2026-11-15): 's own mmap placement and munmap, by full name *)
Module LMm := LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Module LPl := LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.

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

(* The mmap arm of the filtered node relation: its family is off, and its refusals are the errnos. *)
Lemma family_off_pure_mmap : forall l, injected_family_off alloc_forced_cfg (pure_input 222 l) = true.
Proof. intros l. reflexivity. Qed.

Lemma refusal_b_pure_mmap : forall l m r, refusal_b (pure_input 222 l) m r = errno_ret_in mmap_errnos r.
Proof. intros l m r. reflexivity. Qed.

Lemma asem_spurious_of_witness : forall i m eff eff0 m0 evs0,
  injected_family_off alloc_forced_cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (LinuxProcessSemantics.LinuxProcessSem.Monad.Ok eff0 m0 evs0) -> refusal_b i m (eff_ret eff0) = false ->
  spurious_refusal_cfg alloc_forced_cfg i m eff.
Proof.
  intros i m eff eff0 m0 evs0 Hoff Hr Hs Hn.
  split; [exact Hoff | split; [exact Hr | exists eff0, m0, evs0; split; assumption]].
Qed.

(* port727 candidate: the window the grant's gap lies in. At the anonymous grant is Linux's
   placement (LPl.linux_place_is behind place_declined_b); a NULL hint never declines (Lib/Nodes
   place_declined_b_null), and a gap in the bottom-up window [task_unmapped_base, alloc_top) is a placement
   (LPl.linux_place_exists, its right disjunct). The ASan model's gaps lie at or above Spec/Gap's FLOOR, far above
   task_unmapped_base, so the producer meets it (AsanTotal.INV_grant_aok). *)
Definition grant_window (mo : Model) (nZ : Z) : Prop :=
  exists g, LMm.gap_fits (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) LMm.task_unmapped_base
              (alloc_top (m_vmmaps mo)) nZ g.

(* The anonymous grant as a filtered step, and not an errno. *)
Lemma grant_step : forall len mo,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  Mmap.vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  grant_window mo (mmap_len len) ->
  exists a mo', nstepA (NMmap 0 len PROT_RW F_ANON) mo (mkEffectU a [] [(a, Z_to_bv 64 (mmap_len len))] [] [] []) mo' []
    /\ errno_ret_in mmap_errnos a = false.
Proof.
  intros len mo Hlen Htop Hbud Hgap Hwin.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  assert (HnPos : 0 < mmap_len len) by lia.
  assert (HnAl : mmap_len len mod page_size = 0) by (unfold mmap_len; apply LPl.page_round_up_Z_aligned).
  destruct (LPl.linux_place_exists (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) (mmap_len len) HnPos HnAl
              ltac:(destruct Hwin as [g Hg]; exists g; right; exact Hg)) as [p Hp].
  destruct (LPl.linux_place_admissible _ _ _ _ _ HnPos HnAl Hp) as (B1 & B2 & B3 & B4).
  pose proof atop_lt as AL.
  assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  set (a := Z_to_bv 64 p).
  assert (A4 : LPl.linux_place_is (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) (mmap_len len) a = true)
    by (apply LPl.linux_place_is_iff; [exact HnPos| exact HnAl| unfold a; rewrite Up; exact Hp]).
  assert (Ea : errno_ret_in mmap_errnos a = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold a. rewrite Up. unfold two_pow_64. lia. }
  eexists a, _. split; [| exact Ea].
  apply nstepA_mmap_iff. split.
  2:{ apply spurious_refusal_not_refusal. rewrite refusal_b_pure_mmap. exact Ea. }
  unfold check_mmap.
  rewrite G_off, (G_anon F_ANON ltac:(auto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true.
  cbv iota beta. rewrite mmap_len_eq by lia.
  rewrite (place_declined_b_null _ _ _). cbv iota beta zeta.
  rewrite Ea, A4.
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud).
  cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma grant_answers : forall len mo rsp mo' evs,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  Mmap.vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  grant_window mo (mmap_len len) ->
  nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs ->
  evs = [] /\ exists z, adec_mmap atop len PROT_RW rsp = Some z
   /\ z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
   /\ mo' = grant_model mo z (mmap_len len).
Proof.
  intros len mo rsp mo' evs Hlen Htop Hbud Hgap Hwin Hst.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  assert (HnPos : 0 < mmap_len len) by lia.
  assert (HnAl : mmap_len len mod page_size = 0) by (unfold mmap_len; apply LPl.page_round_up_Z_aligned).
  apply -> nstepA_mmap_iff in Hst. destruct Hst as [Hst Hns]. unfold check_mmap in Hst.
  rewrite G_off, (G_anon F_ANON ltac:(auto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true in Hst.
  cbv iota beta in Hst. rewrite mmap_len_eq in Hst by lia.
  rewrite (place_declined_b_null _ _ _) in Hst. cbv iota beta zeta in Hst.
  assert (Er : errno_ret_in mmap_errnos (eff_ret rsp) = false).
  { destruct (errno_ret_in mmap_errnos (eff_ret rsp)) eqn:Er; [|reflexivity]. exfalso. apply Hns.
    destruct (grant_step len mo Hlen Htop Hbud Hgap Hwin) as (a0 & mo0 & Hs0 & Ea0).
    cbn [nstepA node_input] in Hs0. destruct Hs0 as (_ & Hs0 & _).
    apply (asem_spurious_of_witness _ _ _ _ _ _ (family_off_pure_mmap _) (eq_trans (refusal_b_pure_mmap _ _ _) Er) Hs0).
    rewrite refusal_b_pure_mmap. exact Ea0. }
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in Er. cbn [eff_ret] in Hst. rewrite Er in Hst.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  cbv zeta in Hst.
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E Hzs]. apply andb_prop in E as [Hpl Hb].
  destruct (LPl.linux_place_is_admissible _ _ _ _ _ HnPos HnAl Hpl) as (Hal & Hpos & Htp & Hrf).
  apply listNN_eqb_eq in Hzs.
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
  Mmap.vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  grant_window mo (mmap_len len) ->
  exists rsp mo' evs, nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs.
Proof.
  intros len mo Hlen Htop Hbud Hgap Hwin.
  destruct (grant_step len mo Hlen Htop Hbud Hgap Hwin) as (a & mo' & Hs & _). eauto.
Qed.

Lemma fixed_shape : forall flags, (flags = F_FIXED \/ flags = F_FIXNORES) ->
  mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true.
Proof. intros flags [-> | ->]; repeat split; reflexivity. Qed.

(* The fixed-in grant as a filtered step, and not an errno. *)
Lemma fixed_step : forall addr len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  alloc_top (m_vmmaps mo) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  exists mo', nstepA (NMmap addr len PROT_RW flags) mo (mkEffectU (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)] [] [] []) mo' []
    /\ errno_ret_in mmap_errnos (Z_to_bv 64 addr) = false.
Proof.
  intros addr len flags mo Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud.
  assert (Ea : errno_ret_in mmap_errnos (Z_to_bv 64 addr) = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof atop_lt. pose proof (mmap_len_bounds len ltac:(lia)).
    rewrite (unsigned_lit addr) by lia. unfold two_pow_64. lia. }
  eexists _. split; [| exact Ea].
  apply nstepA_mmap_iff. split.
  2:{ apply spurious_refusal_not_refusal. rewrite refusal_b_pure_mmap. exact Ea. }
  unfold check_mmap.
  rewrite G_off, (G_anon flags ltac:(tauto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4. cbv iota beta.
  rewrite mmap_len_eq by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) by lia.
  cbv zeta.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce). unfold page_size. rewrite Hal. rewrite (proj2 (Z.ltb_lt _ _) Ha).
  cbn [negb Z.eqb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  rewrite Ea. cbv iota. rewrite !bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hbud. reflexivity.
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
  apply -> nstepA_mmap_iff in Hst. destruct Hst as [Hst Hns]. unfold check_mmap in Hst.
  rewrite G_off, (G_anon flags ltac:(tauto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4 in Hst. cbv iota beta in Hst.
  rewrite mmap_len_eq in Hst by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) in Hst by lia.
  cbv zeta in Hst.
  replace (two_pow_64 <=? addr + mmap_len len) with false in Hst by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce) in Hst. unfold page_size in Hst. rewrite Hal in Hst. rewrite (proj2 (Z.ltb_lt _ _) Ha) in Hst.
  cbn [negb Z.eqb] in Hst. fold n in Hst. rewrite Hrf, Hmc in Hst. cbn [andb] in Hst.
  assert (Er : errno_ret_in mmap_errnos (eff_ret rsp) = false).
  { destruct (errno_ret_in mmap_errnos (eff_ret rsp)) eqn:Er; [|reflexivity]. exfalso. apply Hns.
    destruct (fixed_step addr len flags mo Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud) as (mo0 & Hs0 & Ea0).
    cbn [nstepA node_input] in Hs0. destruct Hs0 as (_ & Hs0 & _).
    apply (asem_spurious_of_witness _ _ _ _ _ _ (family_off_pure_mmap _) (eq_trans (refusal_b_pure_mmap _ _ _) Er) Hs0).
    rewrite refusal_b_pure_mmap. exact Ea0. }
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in Er. cbn [eff_ret] in Hst. rewrite Er in Hst.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct us; [|discriminate].
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
  destruct (fixed_step addr len flags mo Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud) as (mo' & Hs & _). eauto.
Qed.

(* port727 candidate: 's munmap. (1) Its check answers an errno (the ENOMEM arm) before the kept arm,
   and under alloc_forced_cfg that errno is a spurious refusal whenever the 0-return exact unmap is admitted, so
   the node's own refusal filter rules it out (as the mmap grant's). (2) Its kept arm rebuilds vm_maps with
   maps_subtract over the request (Sys/Mm/Mmap mmap_fixed_destroyed_next), where AsanInv.munmap_model names
   map_remove; the two agree on a separated ledger of nonempty entries (Lib/Decode.dec_maps_subtract_remove), which
   is exactly AsanInv.AMI's own seps and Forall (entry_ok ATOP) conjuncts: aok's AMunmap arm carries those two
   (FORCED by 's munmap; the donor 's form, its anm_ lemmas below). *)
Lemma refusal_b_pure_munmap : forall l m r, refusal_b (pure_input 215 l) m r = errno_ret_in munmap_errnos r.
Proof. intros l m r. reflexivity. Qed.

Lemma family_off_pure_munmap : forall l, injected_family_off alloc_forced_cfg (pure_input 215 l) = true.
Proof. intros l. reflexivity. Qed.

Lemma munmap_errno_zero : errno_ret_in munmap_errnos (Z_to_bv 64 0) = false.
Proof. vm_compute. reflexivity. Qed.

(* The exact unmap as a filtered step, with return 0. *)
Lemma munmap_step0 : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  exists mo', nstepA (NMunmap addr len) mo (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, n)] [] []) mo' [].
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hmh.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  eexists. cbn [nstepA]. apply nstep_munmap_iff. split.
  2:{ apply spurious_refusal_not_refusal. rewrite refusal_b_pure_munmap. exact munmap_errno_zero. }
  unfold check_munmap.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
  rewrite mmap_len_eq by lia. cbv zeta.
  replace (TASK_SIZE <? addr + mmap_len len) with false by (symmetry; apply Z.ltb_ge; lia).
  fold n. rewrite Hmh. rewrite ?munmap_errno_zero. cbv iota beta.
  rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma anm_seps_In2 : forall l x y, seps l -> In x l -> In y l -> x <> y -> wsep x y.
Proof.
  intros l x y Hs. induction Hs as [|p l HF Hs IH]; intros Hx Hy Hne; [destruct Hx|].
  rewrite Forall_forall in HF. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - apply HF. exact Hy.
  - apply wsep_sym. apply HF. exact Hx.
  - apply IH; assumption.
Qed.

Lemma anm_maps_subtract_remove_seps : forall l (a n : word),
  seps l -> Forall (entry_ok atop) l -> map_has l a n = true ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = map_remove l a.
Proof.
  intros l a n Hs Hent Hmh.
  assert (Hin : In (a, n) l).
  { unfold map_has in Hmh. apply existsb_exists in Hmh as ([b0 s0] & Hin0 & He0).
    cbn [fst snd] in He0. apply andb_true_iff in He0 as [H1 H2].
    apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. subst. exact Hin0. }
  assert (Hpos : forall p, In p l -> 0 < bv_unsigned (snd p)).
  { intros p Hp. destruct (proj1 (Forall_forall _ _) Hent p Hp) as (Hp1 & _ & _ & _). exact Hp1. }
  pose proof (Hpos (a, n) Hin) as Hnp. cbn [snd] in Hnp.
  apply (dec_maps_subtract_remove l a n Hnp).
  intros e He Hne. split; [| exact (Hpos e He)].
  pose proof (anm_seps_In2 l e (a, n) Hs He Hin Hne) as W.
  unfold wsep in W. cbn [fst snd] in W. exact W.
Qed.

Lemma munmap_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  seps (vm_maps (m_vmmaps mo)) ->
  Forall (entry_ok atop) (vm_maps (m_vmmaps mo)) ->
  nstepA (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ adec_munmap addr len rsp = Some 0
  /\ mo' = munmap_model mo addr (mmap_len len).
Proof.
  intros addr len mo rsp mo' evs Hlen Ha Hal Hce n Hmh Hsep Hent Hst.
  destruct (munmap_step0 addr len mo Hlen Ha Hal Hce Hmh) as (mo0 & Hs0).
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  cbn [nstepA] in Hst. apply -> nstep_munmap_iff in Hst. destruct Hst as [Hst Hns]. unfold check_munmap in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb] in Hst.
  rewrite mmap_len_eq in Hst by lia. cbv zeta in Hst.
  replace (TASK_SIZE <? addr + mmap_len len) with false in Hst by (symmetry; apply Z.ltb_ge; lia).
  fold n in Hst. rewrite Hmh in Hst.
  assert (Er : errno_ret_in munmap_errnos (eff_ret rsp) = false).
  { destruct (errno_ret_in munmap_errnos (eff_ret rsp)) eqn:Er; [|reflexivity]. exfalso. apply Hns.
    cbn [nstepA nstep node_input] in Hs0. destruct Hs0 as (_ & Hs0 & _).
    apply (asem_spurious_of_witness _ _ _ _ _ _ (family_off_pure_munmap _) (eq_trans (refusal_b_pure_munmap _ _ _) Er) Hs0).
    rewrite refusal_b_pure_munmap. exact munmap_errno_zero. }
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in Er. rewrite Er in Hst. cbv iota beta in Hst.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E1 E2]. unfold w_is0 in E1. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r us.
  split.
  - unfold adec_munmap, dec_munmap. rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. fold n. rewrite !bv_eqb_refl. reflexivity.
  - unfold munmap_model, mmap_fixed_destroyed_next.
    rewrite (anm_maps_subtract_remove_seps (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n Hsep Hent Hmh).
    fold n. subst n. rewrite (unsigned_lit (mmap_len len)) by lia.
    rewrite (unsigned_lit addr) by lia. reflexivity.
Qed.

Lemma munmap_exists : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hmh.
  destruct (munmap_step0 addr len mo Hlen Ha Hal Hce Hmh) as (mo' & Hs). eauto.
Qed.


Definition aok (e : aev) (mo : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      prot = PROT_RW /\ 0 < len <= 2^40 /\ alloc_top (m_vmmaps mo) = atop /\
      if addr =? 0 then
        flags = F_ANON /\ vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo)
        /\ Mmap.vm_gap_available (m_vmmaps mo) (mmap_len len) = true
        (* port727 candidate: + the bottom-up window of 's Linux placement *)
        /\ grant_window mo (mmap_len len)
      else
        (flags = F_FIXED \/ flags = F_FIXNORES) /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | AMunmap addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
      /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
      (* port727 candidate: + AMI's own two conjuncts, for 's maps_subtract rebuild *)
      /\ seps (vm_maps (m_vmmaps mo))
      /\ Forall (entry_ok atop) (vm_maps (m_vmmaps mo))
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
  | _ => False
  end.

Theorem asan_node_sound : node_sound atop nstepA aok apost.
Proof.
  intros e mo Hok. destruct e as [t|b|addr len prot flags|addr len|a l p|w]; try (destruct Hok; fail); try contradiction.
  -
    cbn [aok] in Hok. destruct Hok as (-> & Hlen & Htop & Hc).
    exists (NMmap addr len PROT_RW flags), (adec_mmap atop len PROT_RW). split; [reflexivity|].
    destruct (Z.eqb_spec addr 0) as [->|Hnz].
    + destruct Hc as (-> & Hbud & Hgap & Hwin). split; [|split].
      * intros rsp mo' evs Hst. destruct (grant_answers len mo rsp mo' evs Hlen Htop Hbud Hgap Hwin Hst) as (-> & z & Hd & H1 & H2 & H3 & H4 & ->).
        split; [reflexivity|]. exists z. split; [exact Hd|]. cbn [apost]. rewrite Z.eqb_refl. repeat split; auto.
      * apply grant_exists; auto.
      * intros code mo' Hx. exact Hx.
    + destruct Hc as (Hfl & Ha & Hal & Hce & Hrf & Hmc & Hbud). split; [|split].
      * intros rsp mo' evs Hst. destruct (fixed_answers addr len flags mo rsp mo' evs Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud Hst) as (-> & Hd & ->).
        split; [reflexivity|]. exists addr. split; [exact Hd|]. cbn [apost]. replace (addr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; reflexivity.
      * apply (fixed_exists addr len flags mo); auto.
      * intros code mo' Hx. exact Hx.
  -
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hmh & Hsep & Hent).
    exists (NMunmap addr len), (adec_munmap addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (munmap_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hmh Hsep Hent Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (munmap_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
Qed.

Corollary atotal_STOT_asan : forall {R} (t : AM R) (s : APS) mo (Post : R -> Model -> Prop),
  aps_atop s = atop ->
  atotal aok apost t mo Post ->
  STOT (St:=APS) nstepA (fun R0 => texit (R:=R0) nstepA nexit) (alift t s) mo (fun r s' mo' => s' = s /\ Post r mo').
Proof. intros. apply (atotal_STOT atop nstepA aok apost asan_node_sound); assumption. Qed.
End NodeSem.
