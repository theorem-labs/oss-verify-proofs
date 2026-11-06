From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0u YO0v YO0x YO0j YO0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import AllocSI AllocGS AllocMB AllocRealloc.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AllocMallocMB AllocFreeMB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma map_fbrk z : rg_kind z = RkMap -> f_brkb z = 0.
Proof. intros H. unfold f_brkb, is_brk. rewrite H. destruct (rg_live z); reflexivity. Qed.

Lemma map_fresv z : rg_kind z = RkMap -> f_resvc z = 0.
Proof. intros H. unfold f_resvc, is_resv. rewrite H. reflexivity. Qed.

Lemma rm_rsum f s g am off n rg :
  region_of s (prid (am_mem am)) = Some rg -> rg_kind rg = RkMap -> (forall z, rg_kind z = RkMap -> f z = 0) ->
  rsum f (st_regions (rm_state s g am 0 off n)) = rsum f (st_regions s).
Proof.
  intros Hr Hk Hf. unfold region_of in Hr.
  assert (Hlt : (prid (am_mem am) < length (st_regions s))%nat) by (apply nth_error_Some; congruence).
  pose proof (nth_error_nth _ _ (mkRegion RkMap 0 [] false) Hr) as Hn.
  unfold rm_state. cbn [st_regions set_regions].
  change (st_regions (rm_mid s g am 0 off n)) with (st_regions s ++ [mkRegion RkMap (rm_need n off) [] true]).
  rewrite (rsum_lupd f _ _ _ (mkRegion RkMap 0 [] false)) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by exact Hlt. rewrite Hn, rsum_app, rsum_cons, rsum_nil.
  rewrite (Hf rg Hk), (Hf (mkRegion RkMap (rm_need n off) [] true) eq_refl), (Hf (mkRegion RkMap (rg_len rg) [] false) eq_refl).
  lia.
Qed.

Lemma rm_MB s g am fr n : RMH s g am fr n -> MB s -> MB (rm_state s g am 0 (fr_off fr) n).
Proof.
  intros H HM. destruct (rm_basic s g am fr n H) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rg & Hr & Hrk) & _).
  unfold MB, brk_bytes, resv_count.
  rewrite (rm_rsum f_brkb s g am (fr_off fr) n rg Hr Hrk map_fbrk), (rm_rsum f_resvc s g am (fr_off fr) n rg Hr Hrk map_fresv).
  exact HM.
Qed.

Lemma realloc_MB_direct : forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> yields (realloc (Some p) n s) tr (r, s') -> MB s ->
  MB s' \/ exists tr', yields (realloc_move p n s) tr' (r, s').
Proof.
  intros s p k n tr r s' HW Hin Hn Hy HM.
  destruct (ra_cases answer_ok s p k n tr r s' HW Hin (rpath_yields _ _ _ Hy))
    as [[-> ->] | (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep & C)]; [left; exact HM|].
  destruct C as [(Hc & -> & ->) | [(Hsc & Hbig & Hml & -> & ->) | [(Hsc & Hbig & Hne & -> & ->) | (tr' & Hm)]]].
  - left. exact HM.
  - left. exact HM.
  - left. destruct (rm_of s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig) as [-> R]. exact (rm_MB s g am fr n R HM).
  - right. exists tr'. exact (yields_rpath _ _ _ Hm).
Qed.

Lemma realloc_MB_of
  (HMa : forall s n tr r s', WF s -> MB s -> 0 <= n -> yields (malloc n s) tr (r, s') -> MB s')
  (HFr : forall s p n tr s', WF s -> MB s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') -> MB s') :
  forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> yields (realloc (Some p) n s) tr (r, s') -> MB s -> MB s'.
Proof.
  intros s p k n tr r s' HW Hin Hn Hy HM.
  destruct (realloc_MB_direct s p k n tr r s' HW Hin Hn Hy HM) as [H | (tr' & Hm)]; [exact H|].
  destruct (ra_move answer_ok p n s tr' r s' (rpath_yields _ _ _ Hm)) as (tr1 & q & s1 & H1 & Hq).
  pose proof (yields_rpath _ _ _ H1) as Y1. pose proof (malloc_wf s n tr1 q s1 HW Hn Y1) as HW1.
  pose proof (HMa s n tr1 q s1 HW HM Hn Y1) as HM1.
  pose proof (malloc_blocks s n tr1 q s1 HW Hn Y1) as MB1.
  destruct q as [q|].
  - destruct Hq as (_ & tr2 & H2). destruct MB1 as (l1 & l2 & E1 & E2 & _).
    exact (HFr s1 p k tr2 s' HW1 HM1 (in_after_malloc s s1 l1 l2 q n (p, k) E1 E2 Hin) (yields_rpath _ _ _ H2)).
  - destruct Hq as (_ & ->). exact HM1.
Qed.

Theorem realloc_MB : forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> yields (realloc (Some p) n s) tr (r, s') -> MB s -> MB s'.
Proof. exact (realloc_MB_of AllocMallocMB.malloc_MB AllocFreeMB.free_MB). Qed.
