(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode NodesMm04.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Malloc KInv KStep PState KLink KEv Relim StepB EKPlace Gap.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma nstep_mmap_anon_err_forced : forall len prot mo rsp mo' evs,
  0 < len -> mmap_len len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs ->
  errno_of (eff_ret rsp) <> None ->
  (prot = PROT_RW /\ mmap_grant_refusable (Z_to_bv 64 MAPF) mo (mmap_len len) = true)
  \/ (prot = PROT_NONE /\ mmap_reserve_refusable mo (mmap_len len) = true).
Proof.
  intros len prot mo rsp mo' evs Hlen Hlen2 Hp H He. pose proof (mmap_len_ge len Hlen) as ML.
  destruct (errno_of (eff_ret rsp)) as [e|] eqn:E; [|congruence].
  destruct Hp as [-> | ->].
  - right. split; [reflexivity|].
    destruct (nstep_mmap_none_err_refusable 0 len PROT_NONE MAPF ltac:(lia) mo rsp mo' evs e eq_refl H E) as (_ & R & _). exact R.
  - left. split; [reflexivity|].
    destruct (nstep_mmap_rw_err_refusable 0 len PROT_RW MAPF ltac:(lia) mo rsp mo' evs e eq_refl H E) as (_ & R & _). exact R.
Qed.

(* [comment removed for export] *)
Lemma NF_mmap_anon : forall len prot mo,
  0 < len -> mmap_len len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  vm_live_bytes (m_vmmaps mo) + mmap_len len <= vm_limit (m_vmmaps mo) ->
  vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  NF (NMmap 0 len prot MAPF) mo.
Proof.
  intros len prot mo Hlen Hlen2 Hp Hlz Hmt Hbud Hgap rsp mo' evs Hst.
  destruct (errno_of (eff_ret rsp)) eqn:E; [|reflexivity]. exfalso.
  destruct (nstep_mmap_anon_err_forced len prot mo rsp mo' evs Hlen Hlen2 Hp Hst ltac:(rewrite E; discriminate)) as [[_ R]|[_ R]].
  - rewrite (grant_refusable_false_intro (Z_to_bv 64 MAPF) mo (mmap_len len) eq_refl) in R; [discriminate| | exact Hgap].
    pose proof (backing_le_live mo Hlz Hmt). lia.
  - rewrite (reserve_refusable_false_intro mo (mmap_len len) Hgap) in R. discriminate.
Qed.

(* [comment removed for export] *)
Lemma NF_mmap_fixed : forall a mo,
  let h := m_vmmaps mo in
  0 < a -> a + PGSZ <= alloc_top h -> a mod 4096 = 0 ->
  region_free (vm_reserved h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  NF (NMmap a PGSZ PROT_NONE MAPFX) mo.
Proof.
  intros a mo h Ha Hc Hal Hrf Hmc rsp mo' evs Hst. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT.
  assert (ML : mmap_len PGSZ = PGSZ) by reflexivity.
  destruct (nstep_mmap_fixed_none_no_err a PGSZ PROT_NONE MAPFX ltac:(unfold PGSZ; lia) ltac:(lia) Hal
              ltac:(rewrite ML; lia) mo rsp mo' evs eq_refl Hst) as (E & _ & _).
  exact E.
Qed.

(* [comment removed for export] *)
Lemma NF_mprotect : forall a mo,
  let h := m_vmmaps mo in
  0 <= a -> a + PGSZ < 2^64 -> a mod 4096 = 0 ->
  map_contains (vm_noaccess h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  vm_live_bytes h <= vm_limit h -> minv mo ->
  NF (NMprotect a PGSZ PROT_RW) mo.
Proof.
  intros a mo h Ha Hb Hal Hcn Hcm Hl Hmi rsp mo' evs Hst.
  assert (ML : mmap_len PGSZ = PGSZ) by reflexivity.
  destruct (errno_of (eff_ret rsp)) as [e|] eqn:E; [|reflexivity]. exfalso.
  destruct (nstep_mprotect_err_refusable a PGSZ ltac:(unfold PGSZ; lia) Ha Hal ltac:(rewrite ML; lia) mo rsp mo' evs e Hst E)
    as (_ & _ & _ & _ & _ & R).
  rewrite ML in R. rewrite (mprotect_refusable_false_intro a PGSZ mo) in R; [discriminate|].
  eapply Z.le_trans; [apply backing_le_live| ].
  - unfold mprotect_model_next. rewrite m_vm_lazy_with_vmmaps. apply Hmi.
  - unfold mprotect_model_next. rewrite m_vm_materialized_with_vmmaps. apply Hmi.
  - unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit]. unfold vm_live_bytes in *. cbn [vm_maps]. exact Hl.
Qed.

(* [comment removed for export] *)
Lemma mmap_answer_ok_of_free : forall L pbrk mo a len,
  KL L pbrk mo -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  0 < a -> a mod 4096 = 0 -> a + n <= ld_atop L ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  mmap_answer_ok (ld_atop L) (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo a len HK Hlen h n A2 A1 A3 Hrf. pose proof (KL_atop_lt _ _ _ HK) as Hcl.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split.
  - unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
    rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
    unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
    enough (a + n <= lo \/ lo + m <= a) as D.
    { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
    apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
    + rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
      pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ua, Un in D. exact D.
    + injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
    + injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
    + injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
      rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia.
  - unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.
