(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesMat Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe MSil STree Malloc RawAlloc KInv KLink KStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Realloc ReallocProto MI_LedgerAgree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma region_free_of_disj : forall maps a n,
  (forall e, In e maps -> bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He').
  specialize (H (e, sz) (or_introl eq_refl)). unfold elo, ehi in H; cbn [fst snd] in H.
  unfold iv_overlap. destruct H as [H|H].
  - replace (bv_unsigned e <? bv_unsigned a + bv_unsigned n) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite andb_false_r. reflexivity.
  - replace (bv_unsigned a <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma region_free_app : forall l1 l2 a n,
  region_free l1 a n = true -> region_free l2 a n = true -> region_free (l1 ++ l2) a n = true.
Proof.
  induction l1 as [|[e sz] l1 IH]; intros l2 a n H1 H2; [exact H2|]. cbn [region_free app] in *.
  apply andb_prop in H1 as [H0 H1]. rewrite H0, (IH _ _ _ H1 H2). reflexivity.
Qed.

Lemma region_free_app_l : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof.
  induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn [region_free app] in *.
  apply andb_prop in H as [H0 H]. rewrite H0, (IH _ _ _ H). reflexivity.
Qed.

Lemma region_free_filter : forall f maps a n, region_free maps a n = true -> region_free (List.filter f maps) a n = true.
Proof.
  intros f maps a n H. apply region_free_of_disj. intros e He. apply List.filter_In in He as [He _].
  exact (region_free_disj _ _ _ _ H He).
Qed.

Lemma map_has_In : forall maps e, In e maps -> map_has maps (fst e) (snd e) = true.
Proof.
  intros maps [a n] Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|]. cbn. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma In_map_remove : forall maps aw e, In e (map_remove maps aw) <-> In e maps /\ fst e <> aw.
Proof.
  intros maps aw e. unfold map_remove. rewrite List.filter_In. split.
  - intros [H1 H2]. split; [exact H1|]. intros E. rewrite E, bv_eqb_refl in H2. discriminate.
  - intros [H1 H2]. split; [exact H1|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
Qed.

Lemma nodup_fst_fun : forall (l : list (Z * Z)) M a x y,
  List.NoDup (map fst l ++ M) -> In (a, x) l -> In (a, y) l -> x = y.
Proof.
  intros l M a x y Hnd Hx Hy. apply List.NoDup_app_remove_r in Hnd.
  pose proof (nodup_map_inj fst l (a, x) (a, y) Hnd Hx Hy eq_refl) as E. congruence.
Qed.

Lemma nodup_group_meta : forall (G : list (Z * Z)) (Ms : list (Z * Z * Z)) a x b l k,
  List.NoDup (map fst G ++ map (fun m => fst (fst m)) Ms) -> In (a, x) G -> In (b, l, k) Ms -> b <> a.
Proof.
  intros G Ms a x b l k Hnd Hx Hm ->.
  assert (HinM : In a (map (fun m : Z * Z * Z => fst (fst m)) Ms)) by (apply in_map_iff; exists (a, l, k); auto).
  apply in_split in HinM as (M1 & M2 & E). rewrite E, app_assoc in Hnd.
  apply List.NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. left. apply in_or_app. left.
  apply in_map_iff. exists (a, x). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xev_step_post (L : mled) (e : xev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => xanswer_ok L e z = true /\ KL (xevent_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MREMAP.

Lemma KL_mremap_new : forall L pbrk mo mo' a l nl d,
  KL L pbrk mo -> brk_quiet L -> In (a, l) (ld_groups L) ->
  0 < nl < LEN_MAX -> nl mod PGSZ = 0 ->
  0 < d -> d mod PGSZ = 0 -> d + nl <= alloc_ceiling ->
  let h := m_vmmaps mo in
  region_free (vm_reserved h ++ map_remove (vm_maps h) (wz a)) (wz d) (wz nl) = true ->
  minv mo' -> m_halted mo' = None -> m_vm_materialized mo' = [] ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((wz d, wz nl) :: map_remove (vm_maps h) (wz a))
                 (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KL (set_groups ((d, nl) :: g_remove a (ld_groups L)) L) pbrk mo'
  /\ (forall x, In x (lranges L) -> x = (a, round_up_pg l) \/ d + nl <= fst x \/ fst x + snd x <= d).
Proof.
  intros L pbrk mo mo' a l nl d HK Hq Hin Hnl Hnla Hd Hda Hdc h Hrf Hmi' Hh' Hmat' Evm. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ a l HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
  set (n := mmap_len l) in *. set (aw := wz a) in *. set (dw := wz d) in *. set (nn := wz nl) in *.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_wz; lia).
  assert (Ud : bv_unsigned dw = d) by (subst dw; apply unsigned_wz; lia).
  assert (Un : bv_unsigned nn = nl) by (subst nn; apply unsigned_wz; unfold LEN_MAX in Hnl; lia).
  assert (Hnn : mmap_len nl = nl) by (apply mmap_len_of_aligned; [lia| unfold PGSZ in Hnla; exact Hnla]).
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr. pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (kl_wf _ _ _ HK) as Kwf0. fold h in Kwf0.
  assert (Kfst : forall b l', b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l')) <> aw).
  { intros b l' Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
  assert (Hkeep : forall e, In e (vm_maps h) -> fst e <> aw -> In e (map_remove (vm_maps h) aw)).
  { intros e He Hne. apply In_map_remove. auto. }
  assert (Hsame : forall e, In e (vm_maps h) -> fst e = aw -> e = went a n).
  { intros e He Efst. destruct (pwdisj_In _ _ _ (proj2 Kwf0) He A5) as [E|D]; [exact E|]. exfalso.
    pose proof (proj1 Kwf0 e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W.
    cbn [fst snd went] in D. subst aw. rewrite (unsigned_wz a), (unsigned_wz n) in D by lia. rewrite (unsigned_wz a) in W by lia. lia. }
  assert (Dnew : forall e, In e (vm_maps h) -> fst e <> aw -> d + nl <= elo e \/ ehi e <= d).
  { intros e He Hne. pose proof (region_free_disj _ _ _ _ Hrfm (Hkeep e He Hne)) as D. rewrite Ud, Un in D. exact D. }
  assert (Hcov : forall b0 l0, ld_brkreg L = Some (b0, l0) -> wcov (map_remove (vm_maps h) aw) (b0 + PGSZ) (b0 + l0)).
  { intros b0 l0 E z Hz. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
    intros Efst. rewrite (Hsame e He Efst), B5, B6 in Hr. unfold brk_disj in A6. specialize (A6 b0 l0 E). clear -Hr A6 Hz R3. unfold PGSZ in *. lia. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> d + nl <= b0 + PGSZ \/ b0 + l0 <= d).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & _).
    pose proof (wcov_rf_disj _ _ _ _ _ (Hcov b0 l0 E) Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ud, Un in D. exact D. }
  (* [comment removed for export] *)
  pose proof (kl_distinct _ _ _ HK) as Kd. pose proof Kd as Kd0.
  destruct (g_remove_split a l (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
  rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
  pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
  assert (Hg' : forall b l', In (b, l') (g_remove a (ld_groups L)) -> In (b, l') (ld_groups L) /\ b <> a).
  { intros b l' H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
    intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l'). split; [reflexivity| exact H]. }
  assert (Hm' : forall b l' k, In (b, l', k) (ld_metas L) -> b <> a).
  { intros b l' k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l', k). split; [reflexivity| exact H]. }
  assert (Hnotd : ~ In d ((map fst g1 ++ map fst g2) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros H. rewrite <- map_app, <- Ezz in H. apply in_app_or in H as [H|H].
    - apply in_map_iff in H as ([b l'] & E & H). cbn in E. subst b. destruct (Hg' d l' H) as [H1 Hne].
      pose proof (went_In_bounds _ _ _ d l' HK (or_introl H1)) as (C1 & C2 & C3 & C4 & C5 & C6).
      pose proof (Dnew _ C4 (Kfst d l' Hne ltac:(lia))) as D. rewrite C5, C6 in D. lia.
    - apply in_map_iff in H as ([[b l'] k] & E & H). cbn in E. subst b. pose proof (Hm' d l' k H) as Hne.
      pose proof (went_In_bounds _ _ _ d l' HK (or_intror (ex_intro _ k H))) as (C1 & C2 & C3 & C4 & C5 & C6).
      pose proof (Dnew _ C4 (Kfst d l' Hne ltac:(lia))) as D. rewrite C5, C6 in D. lia. }
  assert (Hph' : phase_inv (ld_brk (set_groups ((d, nl) :: g_remove a (ld_groups L)) L)) (set_groups ((d, nl) :: g_remove a (ld_groups L)) L) pbrk mo').
  { eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]. }
  split.
  2:{ intros x Hx. apply In_lranges in Hx as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
      - right. rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & <- & H). unfold wwZ. cbn [fst snd].
        pose proof (region_free_disj _ _ _ _ Hrfr H) as D. rewrite Ud, Un in D. unfold elo, ehi in D. cbn [fst snd] in D. exact D.
      - subst x. cbn [fst snd]. destruct (Z.eq_dec b1 a) as [->|Hne].
        + left. rewrite (nodup_fst_fun _ _ _ _ _ Kd0 H Hin). reflexivity.
        + right. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (C1 & C2 & C3 & C4 & C5 & C6).
          pose proof (Dnew _ C4 (Kfst b1 l1 Hne ltac:(lia))) as D. rewrite C5, C6 in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
      - subst x. cbn [fst snd]. right. pose proof (Hm' b1 l1 k H) as Hne.
        pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (C1 & C2 & C3 & C4 & C5 & C6).
        pose proof (Dnew _ C4 (Kfst b1 l1 Hne ltac:(lia))) as D. rewrite C5, C6 in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
      - subst x. cbn [fst snd]. right. pose proof (kl_brkreg _ _ _ HK b1 l1 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b1 l1 H). lia. }
  kl_open HK. constructor; try exact Hph'; rewrite ?Evm;
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
  - (* [comment removed for export] *) apply vmwf_cons; [apply vmwf_remove; exact Kwf| rewrite Ud, Un; lia| exact Hrfm].
  - (* [comment removed for export] *) intros b0 l1 [E|Hin0].
    + injection E as <- <-. rewrite Hnn. splits; try lia.
      * left. reflexivity.
      * unfold brk_disj; cbn. exact Dbrk.
    + destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
      right. apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
  - (* [comment removed for export] *) intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0).
    destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
    right. apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
  - (* [comment removed for export] *) cbn [map fst app]. rewrite Ezz, map_app, <- app_assoc. rewrite <- app_assoc in Hnotd. constructor; [exact Hnotd| exact Kd1].
  - (* [comment removed for export] *) intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
    eapply wcov_mono; [| exact (Hcov b0 l1 E)]. intros e He. right. exact He.
  - (* [comment removed for export] *) intros b0 l1 [E|Hin0].
    + injection E as <- <-. rewrite Hnn. intros e He. pose proof (region_free_disj _ _ _ _ Hrfr He) as D. rewrite Ud, Un in D. exact D.
    + destruct (Hg' b0 l1 Hin0) as [Hin1 _]. exact (Kgrv b0 l1 Hin1).
  - (* [comment removed for export] *) intros e He.
    destruct (Kna e He) as [Hm|(b0 & l0 & e0 & E & Q1 & Q2 & He0 & W1 & W2)]; [left; exact Hm| right].
    exists b0, l0, e0. split; [exact E|]. split; [exact Q1|]. split; [exact Q2|]. split; [| split; [exact W1| exact W2]].
    right. apply Hkeep; [exact He0|]. intros Efst.
    pose proof (Kreg b0 l0 E) as (_ & _ & R3 & _).
    rewrite (Hsame e0 He0 Efst), B5 in W1. rewrite (Hsame e0 He0 Efst), B6 in W2.
    unfold brk_disj in A6. specialize (A6 b0 l0 E). clear -W1 W2 A6 R3 B2. unfold PGSZ in *. lia.
  - (* [comment removed for export] *) intros e [<-|He].
    + rewrite elo_pair, ehi_pair, Ud, Un. split; [exact Hda|]. unfold PGSZ in *. rewrite Z.add_mod, Hda, Hnla by lia. reflexivity.
    + apply Kpg. apply In_map_remove in He. exact (proj1 He).
Qed.


(* [comment removed for export] *)
Lemma page_align_is0_false : forall z, 0 < z -> z mod 4096 = 0 -> z < 2^64 -> page_align_is0_b (Z_to_bv 64 z) = false.
Proof.
  intros z Hz Hzm Hzh. unfold page_align_is0_b. rewrite w_is0_lit by lia. rewrite unsigned_lit by lia.
  rewrite page_round_up_Z_id by lia. replace (z =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [orb]. apply Z.leb_gt. unfold two_pow_64. lia.
Qed.

Lemma ev_mremap_ok : forall L G s0 a ol nl fl, frame_ok G ->
  xevent_pre L (XMremap a ol nl fl) ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (xev_step (XMremap a ol nl fl))
        (xev_step_post L (XMremap a ol nl fl) G s0).
Proof.
  intros L G s0 a ol nl fl HG Hpre. cbn [xevent_pre] in Hpre. destruct Hpre as (Hq & -> & (l & Hin & Hol) & Hnl & Hnla & Hne).
  rewrite round_up_pg_eq in Hol. change (page_round_up_Z l) with (mmap_len l) in Hol. subst ol.
  pose proof alloc_ceiling_lt as Hcl. unfold xev_step.
  eapply mspec_bind.
  { apply (mspec_sys (NMremap a (mmap_len l) nl Realloc.MREMAP_MAYMOVE) (dec_mremap a (mmap_len l) nl []) _
             (fun x s mo => s = s0 /\ G s mo
                            /\ KL (xevent_post L (XMremap a (mmap_len l) nl Realloc.MREMAP_MAYMOVE) (mremap_val a x)) (ps_brk s0) mo
                            /\ xanswer_ok L (XMremap a (mmap_len l) nl Realloc.MREMAP_MAYMOVE) (mremap_val a x) = true)).
    intros s mo (-> & HK & HGs).
    pose proof (kl_groups _ _ _ HK a l Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (went_In_bounds _ _ _ a l HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    set (n := mmap_len l) in *.
    set (h := m_vmmaps mo) in *. set (aw := wz a) in *. set (on := wz n). set (nn := wz nl).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_wz; lia).
    assert (Uo : bv_unsigned on = n) by (subst on; apply unsigned_wz; lia).
    assert (Un : bv_unsigned nn = nl) by (subst nn; apply unsigned_wz; unfold LEN_MAX in Hnl; lia).
    assert (Hna : n mod 4096 = 0) by (subst n; apply mmap_len_aligned).
    assert (Hnn : mmap_len nl = nl) by (apply mmap_len_of_aligned; [lia| unfold PGSZ in Hnla; exact Hnla]).
    pose proof (kl_wf _ _ _ HK) as Kwf0. fold h in Kwf0.
    assert (Hsame : forall e, In e (vm_maps h) -> fst e = aw -> e = went a n).
    { intros e He Efst. destruct (pwdisj_In _ _ _ (proj2 Kwf0) He A5) as [E|D]; [exact E|]. exfalso.
      pose proof (proj1 Kwf0 e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W.
      cbn [fst snd went] in D. subst aw. rewrite (unsigned_wz a), (unsigned_wz n) in D by lia. rewrite (unsigned_wz a) in W by lia. lia. }
    (* [comment removed for export] *)
    assert (Hsrc : mremap_source_b h aw on n = true).
    { unfold mremap_source_b. rewrite Ua. fold h. rewrite (minv_alloc_top mo (kl_minv _ _ _ HK)). rewrite (proj2 (Z.leb_le _ _) A4).
      rewrite (region_free_of_disj (vm_reserved h) aw on).
      2:{ intros e He. rewrite Ua, Uo. exact (kl_groups_resv _ _ _ HK a l Hin e He). }
      replace (map_has (vm_maps h) aw on) with true by (symmetry; exact (map_has_In _ _ A5)).
      rewrite (region_free_of_disj (vm_noaccess h) aw on); [reflexivity|].
      intros e He. rewrite Ua, Uo.
      destruct (kl_noacc _ _ _ HK e He) as [(b0 & l0 & k0 & Hm & Q1 & Q2)|(b0 & l0 & e0 & E & Q1 & Q2 & He0 & W1 & W2)].
      - pose proof (nodup_group_meta _ _ _ _ _ _ _ (kl_distinct _ _ _ HK) Hin Hm) as Hneq.
        pose proof (went_In_bounds _ _ _ b0 l0 HK (or_intror (ex_intro _ k0 Hm))) as (C1 & C2 & C3 & C4 & C5 & C6).
        destruct (pwdisj_In _ _ _ (proj2 Kwf0) C4 A5) as [E|D].
        + exfalso. apply Hneq. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
        + unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia.
      - pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (_ & _ & R3 & _).
        destruct (pwdisj_In _ _ _ (proj2 Kwf0) He0 A5) as [E0|D].
        + exfalso. rewrite E0, B5 in W1. rewrite E0, B6 in W2. unfold brk_disj in A6. specialize (A6 b0 l0 E). clear -W1 W2 A6 R3 B2. unfold PGSZ in *. lia.
        + unfold edisj in D. rewrite B5, B6 in D. lia. }
    split.
    { unfold nsafe, mremap_safe_b. fold h aw on nn.
      change (bv_unsigned (Z_to_bv 64 Realloc.MREMAP_MAYMOVE)) with 1. change Uapi.MREMAP_MAYMOVE with 1. cbn [Z.eqb Pos.eqb negb].
      rewrite Ua, page_size_eq. unfold PGSZ in A3. rewrite A3. cbn [Z.eqb negb].
      subst nn on. rewrite (page_align_is0_false nl ltac:(lia) ltac:(unfold PGSZ in Hnla; exact Hnla) ltac:(unfold LEN_MAX in Hnl; lia)).
      rewrite (page_align_is0_false n ltac:(lia) Hna ltac:(lia)).
      rewrite (unsigned_wz n) by lia. rewrite page_round_up_Z_id by lia. rewrite Hsrc.
      unfold mremap_backing_uniform_b. rewrite (minv_lazy _ (kl_minv _ _ _ HK)). reflexivity. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved (NMremap a n nl Realloc.MREMAP_MAYMOVE) _ _ _ _ I (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
    pose proof (nstep_mat_nil _ _ _ _ _ Hst (kl_mat _ _ _ HK)) as Hmat'.
    change Realloc.MREMAP_MAYMOVE with Uapi.MREMAP_MAYMOVE in Hst.
    pose proof (nstep_dec_mremap a n nl [] mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(unfold PGSZ in A3; exact A3)
                  ltac:(lia) Hna ltac:(lia) ltac:(unfold PGSZ in Hnla; exact Hnla) ltac:(unfold LEN_MAX in Hnl; lia) Hsrc (Forall_nil _) Hst)
      as (_ & Hvo & x & Hd & Hx).
    fold h aw on nn in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    cbn [xevent_post xanswer_ok]. unfold mremap_answer_ok.
    destruct x as [e| |d]; cbn [mremap_val].
    - (* [comment removed for export] *) destruct Hx as (-> & -> & _).
      rewrite is_err_neg by (unfold ENOMEM; lia). rewrite is_errno_form_neg by (unfold ENOMEM; lia). split; [exact HK| reflexivity].
    - (* [comment removed for export] *)
      assert (Ea : is_err a = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia). rewrite Ea.
      assert (Ef : is_errno_form a = false) by (unfold is_errno_form, TWO64; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity). rewrite Ef, Z.eqb_refl. cbn [orb andb negb].
      destruct Hx as [[E _]|[[Hlt Evm]|(Hlt & Hg & Evm)]]; [exfalso; exact (Hne (eq_sym E))| |].
      + (* [comment removed for export] *)
        assert (Hrf : region_free (vm_reserved h ++ map_remove (vm_maps h) aw) aw nn = true).
        { apply region_free_app.
          - apply region_free_of_disj. intros e He. rewrite Ua, Un. pose proof (kl_groups_resv _ _ _ HK a l Hin e He). lia.
          - apply region_free_of_disj. intros e He. rewrite Ua, Un. apply In_map_remove in He as [He Hfst].
            destruct (pwdisj_In _ _ _ (proj2 Kwf0) He A5) as [E|D]; [exfalso; apply Hfst; rewrite E; reflexivity|].
            unfold edisj in D. rewrite B5, B6 in D. lia. }
        destruct (KL_mremap_new L (ps_brk s0) mo mo' a l nl a HK Hq Hin Hnl Hnla A2 A3 ltac:(lia) Hrf Hmi' Hh' Hmat' Evm) as [HK' _].
        split; [exact HK'|]. rewrite (proj2 (Z.ltb_lt _ _) Hlt). reflexivity.
      + (* [comment removed for export] *)
        unfold mremap_inplace_grow_b in Hg. fold h in Hg. rewrite Ua in Hg. apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hc Hrf]. apply Z.leb_le in Hc.
        rewrite (minv_alloc_top mo (kl_minv _ _ _ HK)) in Hc.
        destruct (KL_mremap_new L (ps_brk s0) mo mo' a l nl a HK Hq Hin Hnl Hnla A2 A3 Hc Hrf Hmi' Hh' Hmat' Evm) as [HK' Hfree].
        split; [exact HK'|]. rewrite (proj2 (Z.leb_le _ _) Hc). replace (nl <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb andb].
        rewrite orb_false_r. unfold ranges_free. apply forallb_forall. intros [lo m] Hlm. cbn [fst snd]. unfold iv_disjoint.
        enough (a + nl <= lo \/ lo + m <= a + n) as D.
        { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity| rewrite (proj2 (Z.leb_le (lo + m) (a + n))) by lia; apply orb_true_r]. }
        destruct (Hfree _ Hlm) as [E|D]; [injection E as -> ->| cbn [fst snd] in D; lia]. right. rewrite round_up_pg_eq. fold (mmap_len l). fold n. lia.
    - (* [comment removed for export] *)
      destruct Hx as (Hlt & Hdst & Hrf0 & Evm). apply mremap_dst_ok_true in Hdst as [(D1 & D2 & D3 & D4) _]. rewrite page_size_eq in D1.
      assert (Ed : is_err d = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia). rewrite Ed.
      assert (Ef : is_errno_form d = false) by (unfold is_errno_form, TWO64; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity). rewrite Ef.
      replace (d =? a) with false by (symmetry; apply Z.eqb_neq; exact D4). cbn [orb andb negb].
      assert (Hrf : region_free (vm_reserved h ++ map_remove (vm_maps h) aw) (wz d) nn = true).
      { apply region_free_app; [exact (region_free_app_l _ _ _ _ Hrf0)|]. unfold map_remove. apply region_free_filter. exact (region_free_app_r _ _ _ _ Hrf0). }
      destruct (KL_mremap_new L (ps_brk s0) mo mo' a l nl d HK Hq Hin Hnl Hnla D2 ltac:(unfold PGSZ; exact D1) D3 Hrf Hmi' Hh' Hmat' Evm) as [HK' Hfree].
      split; [exact HK'|]. rewrite (proj2 (Z.ltb_lt 0 d) D2). unfold PGSZ. rewrite D1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) D3). cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hlm. cbn [fst snd]. unfold iv_disjoint.
      enough (d + nl <= lo \/ lo + m <= d) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity| rewrite (proj2 (Z.leb_le (lo + m) d)) by lia; apply orb_true_r]. }
      destruct (Hfree _ Hlm) as [E|D]; [injection E as -> ->| cbn [fst snd] in D; exact D].
      rewrite round_up_pg_eq. fold (mmap_len l). fold n.
      pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf0) A5) as D. rewrite B5, B6, (unsigned_wz d), Un in D by lia. exact D. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & Hans). unfold xev_step_post. splits; auto.
Qed.

End MREMAP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint xctree_ok {R} (L : mled) (t : MX R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => xevent_pre L e /\ forall z, xanswer_ok L e z = true -> xctree_ok (xevent_post L e z) (k z) Post
  end.

Lemma ptreeX_xctree_ok {R} : forall (t : MX R) L Post, ptreeX L t Post -> xctree_ok L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ptreeX xctree_ok] in *; [exact H|].
  destruct e as [e'|]; [destruct e'|]; try (destruct H; fail); try contradiction;
    (destruct H as [He Hk]; split; [exact He|]; intros z Hz; specialize (Hk z); rewrite Hz in Hk; apply IH; exact Hk).
Qed.

Lemma xctree_ok_mono {R} : forall (t : MX R) L (P Q : mled -> R -> Prop),
  (forall L' r, P L' r -> Q L' r) -> xctree_ok L t P -> xctree_ok L t Q.
Proof.
  induction t as [r|e k IH]; intros L P Q HPQ H; cbn [xctree_ok] in *; [auto|].
  destruct H as [He Hk]. split; [exact He|]. intros z Hz. eapply IH; [exact HPQ| apply Hk; exact Hz].
Qed.

(* [comment removed for export] *)
Lemma xctree_ok_xlift {R} : forall (t : M R) L Post, ctree_ok L t Post -> xctree_ok L (xlift t) Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ctree_ok xctree_ok xlift] in *; [exact H|].
  destruct H as [He Hk]. split; [exact He|]. intros z Hz. apply IH. apply Hk. exact Hz.
Qed.

Lemma xev_step_spec : forall L e (G : PState -> Model -> Prop) s0,
  frame_ok G -> xevent_pre L e ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (xev_step e) (xev_step_post L e G s0).
Proof.
  intros L e G s0 HG Hpre. destruct e as [e|a ol nl fl].
  - cbn [xev_step]. exact (ev_step_spec L e G s0 HG Hpre).
  - apply ev_mremap_ok; assumption.
Qed.

Lemma xmembed_spec {R} : forall (t : MX R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> xctree_ok L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (xmembed t)
        (fun r s mo => exists L', xcpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [xmembed]. apply mspec_ret. intros s mo (-> & HK & HGs). exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [xmembed]. cbn [xctree_ok] in Hok. destruct Hok as [Hpre Hk].
    eapply mspec_bind; [apply (xev_step_spec L e G s0 HG Hpre)|].
    intros z. unfold xev_step_post. apply mspec_pointwise. intros s1 mo1 (Hans & HK1 & HG1 & Hm & Hfa & Hso).
    eapply mspec_conseq; [apply (IH z Post G (xevent_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tmm_ev_step : forall e s, tmm (ev_step e s).
Proof.
  intros e s. destruct e; cbn [ev_step];
    repeat (first [ apply tmm_mif | apply tmm_mbind | apply tmm_msys | apply tmm_mret | apply tmm_munr | apply tmm_mget | apply tmm_mupd | exact I ]; intros);
    try (match goal with |- tmm (match ?a with _ => _ end _) => destruct a end;
         repeat (first [ apply tmm_mbind | apply tmm_mret | apply tmm_mupd | exact I ]; intros)).
Qed.

Lemma tmm_membed {R} : forall (t : stree ev Z R) s, tmm (membed t s).
Proof.
  induction t as [r|e k IH]; intros s; cbn [membed]; [apply tmm_mret|].
  apply tmm_mbind; [apply tmm_ev_step| intros; apply IH].
Qed.

Lemma tmm_xev_step : forall e s, tmm (xev_step e s).
Proof.
  intros [e|a ol nl fl] s; cbn [xev_step]; [apply tmm_ev_step|].
  apply tmm_mbind; [apply tmm_msys; exact I| intros; apply tmm_mret].
Qed.

Lemma tmm_xmembed {R} : forall (t : MX R) s, tmm (xmembed t s).
Proof.
  induction t as [r|e k IH]; intros s; cbn [xmembed]; [apply tmm_mret|].
  apply tmm_mbind; [apply tmm_xev_step| intros; apply IH].
Qed.

Lemma tmm_raw_malloc : forall n s, tmm (raw_malloc n s).
Proof.
  intros n s. unfold raw_malloc. apply tmm_mbind; [apply tmm_mget|]. intros cs s1.
  apply tmm_mbind; [apply tmm_membed|]. intros [st' p] s2. apply tmm_mbind; [apply tmm_mupd|]. intros; apply tmm_mret.
Qed.

Lemma tmm_raw_free : forall p s, tmm (raw_free p s).
Proof.
  intros p s. unfold raw_free. apply tmm_mbind; [apply tmm_mget|]. intros cs s1.
  apply tmm_mbind; [apply tmm_membed|]. intros; apply tmm_mupd.
Qed.

(* [comment removed for export] *)
Theorem membed_tsil {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0 mo,
  frame_ok G -> ctree_ok L t Post -> KL L (ps_brk s0) mo -> G s0 mo ->
  tsil (membed t s0) mo
       (fun p mo' => match p with
                     | Unr => False
                     | Ok (r, s) => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo' /\ G s mo'
                                   /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0
                     end).
Proof.
  intros t Post G L s0 mo HG Hok HK HGs.
  eapply tsil_mono; [apply (mspec_tsil _ _ _ s0 mo (membed_spec t Post G L s0 HG Hok)); [auto| apply tmm_membed]|].
  intros [|[r s]] mo'; cbn; auto.
Qed.

Theorem xmembed_tsil {R} : forall (t : MX R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0 mo,
  frame_ok G -> xctree_ok L t Post -> KL L (ps_brk s0) mo -> G s0 mo ->
  tsil (xmembed t s0) mo
       (fun p mo' => match p with
                     | Unr => False
                     | Ok (r, s) => exists L', xcpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo' /\ G s mo'
                                   /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0
                     end).
Proof.
  intros t Post G L s0 mo HG Hok HK HGs.
  eapply tsil_mono; [apply (mspec_tsil _ _ _ s0 mo (xmembed_spec t Post G L s0 HG Hok)); [auto| apply tmm_xmembed]|].
  intros [|[r s]] mo'; cbn; auto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem KL_agree : forall L1 L2 pbrk mo, ledger_agree L1 L2 -> KL L1 pbrk mo -> KL L2 pbrk mo.
Proof.
  intros L1 L2 pbrk mo (Er & Pg & Pm & Eb & Ep) HK.
  assert (Hg : forall x, In x (ld_groups L2) -> In x (ld_groups L1)).
  { intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact Pg| exact Hx]. }
  assert (Hm : forall x, In x (ld_metas L2) -> In x (ld_metas L1)).
  { intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact Pm| exact Hx]. }
  assert (Hm' : forall x, In x (ld_metas L1) -> In x (ld_metas L2)).
  { intros x Hx. eapply Permutation_in; [exact Pm| exact Hx]. }
  assert (Hbd : forall b n, brk_disj L1 b n -> brk_disj L2 b n).
  { intros b n H. unfold brk_disj in *. rewrite <- Eb. exact H. }
  kl_open HK. constructor; auto.
  - rewrite <- Er. exact Kresv.
  - intros b l Hin. specialize (Kgr b l (Hg _ Hin)). intuition auto.
  - intros b l k Hin. specialize (Kme b l k (Hm _ Hin)). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; auto.
  - eapply Permutation_NoDup; [| exact Kdis]. apply Permutation_app; apply Permutation_map; assumption.
  - intros b l E. rewrite <- Eb in E. exact (Kreg b l E).
  - rewrite <- Ep, <- Eb. destruct (ld_brk L1); try exact Kph.
    destruct Kph as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). splits; auto.
    all: first [ intros bb ll kk Hin'; exact (P8 bb ll kk (Hm _ Hin')) | intros bb ll Hin'; exact (P7 bb ll (Hg _ Hin')) ].
  - intros e He. rewrite <- Eb. destruct (Kna e He) as [(b & l & k & Hin & Q)|H]; [left; exists b, l, k; split; [apply Hm'; exact Hin| exact Q]| right; exact H].
Qed.
End RC__1.
