(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed aok, asan_node_sound, grant_answers and 4 more; added anm_iv_subtract_apart, anm_iv_subtract_self, anm_map_remove_cons and 4 more; taken in part from projects/simdjson/fuzz_parser/proofs/lib/Spec/AsanNodeSem.v, 59 lines within its lines 10-439. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import NodesA.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Cfg MmEd.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import STree AsanCtrl AsanEmbed Monad RSim AsanProgDeps AsanTotalCore AsanInv.
Import ListNotations.
Open Scope Z_scope.

Lemma mmap_len_eq : forall len, 0 <= len < 2^63 -> page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = mmap_len len.
Proof. intros. unfold mmap_len. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma mmap_len_bounds : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. pose proof (Z.div_mod (l + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Lemma nstepA_mmap_ed : forall addr len prot flags mo eff mo' evs,
  nstepA (NMmap addr len prot flags) mo eff mo' evs ->
  mmap_corner_free (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) mo eff ->
  check_mmap_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs.
Proof.
  intros addr len prot flags mo eff mo' evs H Hcf. apply nstepA_mmap_iff in H as [H Hns].
  cbn [mm_ns node_input] in Hns.
  apply check_mmap_ed_fwd; [exact H| | exact Hcf].
  exact (forced_of_ns_mmap (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                                            Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff ltac:(reflexivity) Hns).
Qed.

Lemma nstepA_mmap_of_ed : forall addr len prot flags mo eff mo' evs,
  check_mmap_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs ->
  nstepA (NMmap addr len prot flags) mo eff mo' evs.
Proof.
  intros addr len prot flags mo eff mo' evs H.
  destruct (ns_of_check_mmap_ed
              (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                               Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff mo' evs ltac:(reflexivity) H) as [Hc Hns].
  apply nstepA_mmap_iff. split; [|exact Hns].
  rewrite check_syscall_mmap in Hc by reflexivity. exact Hc.
Qed.

(* LPS 75d69e00: a placement Linux makes is one the checker's search finds (text of fuzz_parser's
   Lib/NodesMm04.v; this unit has no NodesMm04). *)
Lemma place_found_of_place : forall m addr nZ,
  0 < nZ -> nZ mod page_size = 0 ->
  (exists a, linux_place (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ a) ->
  mmap_place_found m addr nZ = true.
Proof.
  intros m addr nZ Hp Ha [a Hl]. unfold mmap_place_found.
  destruct (Placement.linux_place_b (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ) eqn:E; [reflexivity|].
  exfalso. exact (proj1 (proj2 (Placement.linux_place_b_spec _ _ _ _ Hp Ha)) E a Hl).
Qed.

Section NodeSem.
Variable atop : Z.                         (* [comment removed for export] *)
Hypothesis Hatop : atop_ok atop.           (* [comment removed for export] *)

Let atop_lt : atop < 2^47.
Proof. destruct Hatop as [_ H]. unfold ATOP_MAX in H. lia. Qed.

(* [comment removed for export] *)
Let G_off : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false. Proof. reflexivity. Qed.
Let G_anon : forall flags, (flags = F_ANON \/ flags = F_FIXED \/ flags = F_FIXNORES) -> negb (mmap_anon_b (Z_to_bv 64 flags)) = false.
Proof. intros flags [-> |[-> | ->]]; reflexivity. Qed.

Lemma grant_answers : forall len mo rsp mo' evs,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  (* LPS 75d69e00: the modeled arm places by Linux's search at the NULL hint *)
  mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true ->
  nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs ->
  evs = [] /\ exists z, adec_mmap atop len PROT_RW rsp = Some z
   /\ z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
   /\ mo' = grant_model mo z (mmap_len len).
Proof.
  intros len mo rsp mo' evs Hlen Htop Hbud Hpl Hst.
  apply nstepA_mmap_ed in Hst; [| apply mmap_corner_free_not_rw; vm_compute; reflexivity].
  unfold check_mmap_ed in Hst.
  rewrite G_off, (G_anon F_ANON ltac:(auto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true in Hst.
  (* LPS 727298f3 (#146): the NULL hint is never declined *)
  cbv iota beta in Hst. rewrite place_declined_b_null in Hst. cbv iota in Hst. rewrite mmap_len_eq in Hst by lia.
  assert (Hnr : mmap_grant_refusable_at (Z_to_bv 64 F_ANON) mo (Z_to_bv 64 0) (mmap_len len) = false).
  { unfold mmap_grant_refusable_at. rewrite Hpl. unfold mmap_noreserve_backed_ok.
    change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity. }
  rewrite Hnr in Hst. change (mmap_errnos_when false) with (@nil Z) in Hst. cbn [errno_ret_in existsb] in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  cbv zeta in Hst.
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  (* LPS 75d69e00: the grant test is Linux's placement; its admissibility gives the four facts *)
  apply andb_prop in E as [E Hzs]. apply andb_prop in E as [Epl Hb]. apply listNN_eqb_eq in Hzs.
  assert (NP : 0 < mmap_len len) by (pose proof (mmap_len_bounds len ltac:(lia)); lia).
  assert (NA : mmap_len len mod page_size = 0) by (unfold mmap_len, page_round_up_Z; apply Z_mod_mult).
  destruct (Placement.linux_place_is_admissible _ _ _ _ _ NP NA Epl) as (Hal & Hpos & Htp & Hrf).
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
  mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true ->
  exists rsp mo' evs, nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs.
Proof.
  intros len mo Hlen Htop Hbud Hpl.
  (* LPS 75d69e00: the granting answer is Linux's own placement *)
  assert (NP : 0 < mmap_len len) by (pose proof (mmap_len_bounds len ltac:(lia)); lia).
  assert (NA : mmap_len len mod page_size = 0) by (unfold mmap_len, page_round_up_Z; apply Z_mod_mult).
  destruct (place_found_witness mo (Z_to_bv 64 0) (mmap_len len) NP NA Hpl) as (a & Hpa & _).
  eexists (mkEffectU a [] [(a, Z_to_bv 64 (mmap_len len))] [] [] []), _, [].
  apply nstepA_mmap_of_ed. unfold check_mmap_ed.
  rewrite G_off, (G_anon F_ANON ltac:(auto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true.
  cbv iota beta. rewrite place_declined_b_null. cbv iota. rewrite mmap_len_eq by lia.
  assert (Hnr : mmap_grant_refusable_at (Z_to_bv 64 F_ANON) mo (Z_to_bv 64 0) (mmap_len len) = false).
  { unfold mmap_grant_refusable_at. rewrite Hpl. unfold mmap_noreserve_backed_ok.
    change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity. }
  rewrite Hnr. change (mmap_errnos_when false) with (@nil Z). cbn [errno_ret_in existsb]. cbv zeta.
  rewrite Hpa.
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud).
  cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma fixed_shape : forall flags, (flags = F_FIXED \/ flags = F_FIXNORES) ->
  mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true.
Proof. intros flags [-> | ->]; repeat split; reflexivity. Qed.

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
  apply nstepA_mmap_ed in Hst;
    [| unfold mmap_corner_free; intros _; right; rewrite mmap_len_eq by lia; fold n; rewrite Hrf, Hmc;
       split; [reflexivity| exact Hbud]].
  unfold check_mmap_ed in Hst.
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
  rewrite Hnr in Hst. change (mmap_errnos_when false) with (@nil Z) in Hst. change mmap_destructive_errnos with (@nil Z) in Hst.
  cbn [errno_ret_in existsb andb] in Hst. cbv iota in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
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
  eexists (mkEffectU (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)] [] [] []), _, [].
  apply nstepA_mmap_of_ed. unfold check_mmap_ed.
  rewrite G_off, (G_anon flags ltac:(tauto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4. cbv iota beta.
  rewrite mmap_len_eq by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) by lia.
  cbv zeta.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce). unfold page_size. rewrite Hal. rewrite (proj2 (Z.ltb_lt _ _) Ha).
  cbn [negb Z.eqb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  assert (Hnr : mmap_fixed_commit_refusable (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = false).
  { unfold mmap_fixed_commit_refusable. rewrite Hbud. reflexivity. }
  rewrite Hnr. change (mmap_errnos_when false) with (@nil Z). change mmap_destructive_errnos with (@nil Z).
  cbn [errno_ret_in existsb andb]. cbv iota. rewrite !bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hbud. reflexivity.
Qed.

(* LPS 75d69e00: the kept [munmap] arm rebuilds [vm_maps] with [maps_subtract]
   over the request (through [Mmap.mmap_fixed_destroyed_next], model
   Sys/Mm/Mmap.v:1488) where [AsanInv.munmap_model] names [map_remove].  On a
   separated ledger of nonempty entries the two agree; [AsanInv.AMI] carries both
   facts ([seps (vm_maps ...)] and [Forall (entry_ok ATOP) (vm_maps ...)]), so [aok]
   carries them and [AsanTotal.INV_munmap_aok] discharges both by projection.
   Text of fuzz_parser's Lib/Decode.v and Spec/AsanNodeSem.v (the [anm_] prefix
   keeps these clear of other files' names on the same import path). *)
Lemma anm_iv_subtract_self : forall (aw nw : word),
  iv_subtract aw nw (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = [].
Proof.
  intros aw nw. unfold iv_subtract. cbv zeta.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned aw) (bv_unsigned aw))) by lia.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned aw + bv_unsigned nw) (bv_unsigned aw + bv_unsigned nw))) by lia.
  reflexivity.
Qed.

Lemma anm_iv_subtract_apart : forall (b s aw nw : word),
  0 < bv_unsigned s ->
  bv_unsigned b + bv_unsigned s <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= bv_unsigned b ->
  iv_subtract b s (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = [(b, s)].
Proof.
  intros b s aw nw Hs D.
  pose proof (bv_unsigned_in_range 64 b). pose proof (bv_unsigned_in_range 64 s).
  pose proof (bv_unsigned_in_range 64 aw). pose proof (bv_unsigned_in_range 64 nw).
  unfold iv_subtract. cbv zeta. destruct D as [D|D].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned aw))) by lia.
    rewrite (proj2 (Z.ltb_ge (bv_unsigned aw + bv_unsigned nw) (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) (bv_unsigned aw))) by lia.
    rewrite (proj2 (Z.ltb_lt (bv_unsigned aw + bv_unsigned nw) (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b) with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma anm_map_remove_cons : forall e l (aw : word),
  map_remove (e :: l) aw = (if bv_eqb (fst e) aw then [] else [e]) ++ map_remove l aw.
Proof. intros e l aw. unfold map_remove. cbn [List.filter]. destruct (bv_eqb (fst e) aw); reflexivity. Qed.

Lemma anm_maps_subtract_remove : forall l (aw nw : word),
  0 < bv_unsigned nw ->
  (forall e, In e l -> e <> (aw, nw) ->
     (bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned aw
      \/ bv_unsigned aw + bv_unsigned nw <= bv_unsigned (fst e))
     /\ 0 < bv_unsigned (snd e)) ->
  maps_subtract l (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = map_remove l aw.
Proof.
  intros l aw nw Hn. induction l as [|[b s] l IH]; intros Hap; [reflexivity|].
  cbn [maps_subtract]. rewrite anm_map_remove_cons. cbn [fst].
  rewrite IH by (intros e He Hne; apply Hap; [right; exact He| exact Hne]).
  destruct (bv_eqb b aw) eqn:E.
  - apply bv_eqb_eq in E. subst b. destruct (bv_eqb s nw) eqn:Es.
    + apply bv_eqb_eq in Es. subst s. rewrite anm_iv_subtract_self. reflexivity.
    + exfalso.
      assert (Hne : (aw, s) <> (aw, nw))
        by (intros EE; apply (f_equal snd) in EE; cbn [snd] in EE; rewrite EE, bv_eqb_refl in Es; discriminate).
      destruct (Hap (aw, s) (or_introl eq_refl) Hne) as [D Hs]. cbn [fst snd] in D, Hs. lia.
  - assert (Hne : (b, s) <> (aw, nw))
      by (intros EE; apply (f_equal fst) in EE; cbn [fst] in EE; rewrite EE, bv_eqb_refl in E; discriminate).
    destruct (Hap (b, s) (or_introl eq_refl) Hne) as [D Hs]. cbn [fst snd] in D, Hs.
    rewrite (anm_iv_subtract_apart b s aw nw Hs D). reflexivity.
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
  apply (anm_maps_subtract_remove l a n Hnp).
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
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  cbn [nstepA] in Hst. pose proof (nstep_munmap_nonrefusal _ _ _ _ _ _ Hst) as Hnr.
  apply nstep_munmap_check in Hst. unfold check_munmap in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb] in Hst.
  rewrite mmap_len_eq in Hst by lia. cbv zeta in Hst.
  replace (TASK_SIZE <? addr + mmap_len len) with false in Hst by (symmetry; apply Z.ltb_ge; lia).
  fold n in Hst. rewrite Hmh in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  (* LPS 08b1429: the injected -ENOMEM is excluded by [Hnr]. *)
  cbn [eff_ret] in Hnr. rewrite Hnr in Hst. cbv beta iota in Hst.
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
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  eexists (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, n)] [] []), _, [].
  cbn [nstepA]. apply nstep_munmap_iff.
  split; [|cbn [mm_ns node_input]; apply munmap_ret_not_spurious; cbn [eff_ret]; vm_compute; reflexivity].
  unfold check_munmap.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
  rewrite mmap_len_eq by lia. cbv zeta.
  replace (TASK_SIZE <? addr + mmap_len len) with false by (symmetry; apply Z.ltb_ge; lia).
  fold n. rewrite Hmh. replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma madvise_next_canon : forall mo a n, m_vm_materialized mo = [] -> madvise_dontneed_next mo a n = mo.
Proof.
  intros mo a n H. unfold madvise_dontneed_next. rewrite H. cbn [List.filter]. rewrite <- H.
  destruct mo as [fd [mp lz mt] io fs pr lm tm]. reflexivity.
Qed.

Lemma madvise_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= 2^47 ->
  let n := Z_to_bv 64 (mmap_len len) in
  m_vm_materialized mo = [] ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) n = true ->
  nstepA (NMadvise addr len) mo rsp mo' evs ->
  evs = [] /\ adec_madvise addr len rsp = Some 0 /\ mo' = mo.
Proof.
  intros addr len mo rsp mo' evs Hlen Ha Hal Hce n Hcan Hok Hst.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  cbn [nstepA] in Hst. apply nstep_madvise_iff in Hst. unfold check_madvise in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst.
  change (negb (madvise_dontneed_b (Z_to_bv 64 4))) with false in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb Z.eqb] in Hst. cbv iota in Hst.
  rewrite mmap_len_eq in Hst by lia.
  replace (two_pow_64 <=? addr + mmap_len len) with false in Hst by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  cbv zeta iota in Hst. fold n in Hst. rewrite Hok in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E1 E2]. unfold w_is0 in E1. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r zs.
  split.
  - unfold adec_madvise, dec_madvise, dec_mprotect. rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. fold n. rewrite !bv_eqb_refl.
    replace (errno_of (Z_to_bv 64 0)) with (@None Z) by reflexivity. reflexivity.
  - apply madvise_next_canon. exact Hcan.
Qed.

Lemma madvise_exists : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= 2^47 ->
  let n := Z_to_bv 64 (mmap_len len) in
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMadvise addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hok.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  eexists (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, n)] [] [] []), _, [].
  cbn [nstepA]. apply nstep_madvise_iff. unfold check_madvise.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal.
  change (negb (madvise_dontneed_b (Z_to_bv 64 4))) with false.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb Z.eqb]. cbv iota.
  rewrite mmap_len_eq by lia.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  cbv zeta iota. fold n. rewrite Hok. rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aok (e : aev) (mo : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      prot = PROT_RW /\ 0 < len <= 2^40 /\ alloc_top (m_vmmaps mo) = atop /\
      if addr =? 0 then
        flags = F_ANON /\ vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo)
        (* LPS 75d69e00: Linux places the call at the NULL hint *)
        /\ mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true
      else
        (flags = F_FIXED \/ flags = F_FIXNORES) /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | AMunmap addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
      /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
      (* LPS 75d69e00: the kept arm's [maps_subtract] rebuild agrees with [munmap_model]'s
         [map_remove] on a separated ledger of nonempty entries ([AsanInv.AMI]'s own facts) *)
      /\ seps (vm_maps (m_vmmaps mo))
      /\ Forall (entry_ok atop) (vm_maps (m_vmmaps mo))
  | AMadvise addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= 2^47
      /\ m_vm_materialized mo = []
      /\ madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
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
  | AMadvise addr len => z = 0 /\ mo' = mo
  | _ => False
  end.

Theorem asan_node_sound : node_sound atop nstepA aok apost.
Proof.
  intros e mo Hok. destruct e as [t|b|addr len prot flags|addr len|a l p|addr len|w]; try (destruct Hok; fail); try contradiction.
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hmh & Hsep & Hent).
    exists (NMunmap addr len), (adec_munmap addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (munmap_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hmh Hsep Hent Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (munmap_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
  - (* [comment removed for export] *)
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hcan & Hmok).
    exists (NMadvise addr len), (adec_madvise addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (madvise_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hcan Hmok Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (madvise_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
Qed.

(* [comment removed for export] *)
Corollary atotal_STOT_asan : forall {R} (t : AM R) (s : APS) mo (Post : R -> Model -> Prop),
  aps_atop s = atop ->
  atotal aok apost t mo Post ->
  STOT (St:=APS) nstepA (fun R0 => texit (R:=R0) nstepA nexit) (alift t s) mo (fun r s' mo' => s' = s /\ Post r mo').
Proof. intros. apply (atotal_STOT atop nstepA aok apost asan_node_sound); assumption. Qed.
End NodeSem.
