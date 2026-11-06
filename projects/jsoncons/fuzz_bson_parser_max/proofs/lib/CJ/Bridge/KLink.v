(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import Prelim Monad STree Malloc Prog KInv KStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pwdisj_In : forall l e1 e2, pwdisj l -> In e1 l -> In e2 l -> e1 = e2 \/ edisj e1 e2.
Proof.
  induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
  inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. apply H3. exact H2.
  - right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
  - apply IH; assumption.
Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

Lemma vmwf_cons : forall maps a n, vmwf maps ->
  bv_unsigned a < bv_unsigned a + bv_unsigned n <= 2^64 ->
  region_free maps a n = true ->
  vmwf ((a, n) :: maps).
Proof.
  intros maps a n [Hb Hp] Hn Hrf. split.
  - intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
  - constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn. lia.
Qed.

Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
  - constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply IH; assumption.
Qed.

Lemma vmwf_remove : forall maps a, vmwf maps -> vmwf (map_remove maps a).
Proof.
  intros maps a [Hb Hp]. unfold map_remove. split.
  - intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply pwdisj_filter. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz).
  unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) (lo)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In : forall maps lo hi e, In e (maps_subtract maps lo hi) ->
  exists e0, In e0 maps /\ In e (iv_subtract (fst e0) (snd e0) lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity| exact Hin].
  - destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall a sz lo hi,
  bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 -> lo < hi ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keep : forall maps lo hi e, vmwf maps -> lo < hi ->
  In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
  destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_contains : forall a sz lo hi x y,
  lo < hi -> 0 <= lo -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlh Hlo Hwf Hax Hxy Hy Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn. rewrite unsigned_lit by lia. lia.
  - replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In_intro : forall maps lo hi e e', In e maps -> In e' (iv_subtract (fst e) (snd e) lo hi) ->
  In e' (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.

Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
  induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
  - apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi -> 0 <= lo -> bv_unsigned a + bv_unsigned sz <= 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlh Hlo Hwf. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) (lo)); destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, lo < hi -> 0 <= lo -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh Hlo [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlh Hlo Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlh| exact Hlo| lia]| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KL2DEF.
Variable resv_img : list (word * word).   (* [comment removed for export] *)
Variable img_hi : Z.                      (* [comment removed for export] *)

Record KL2 (L : mled) (pbrk : Z) (h : VmMaps) : Prop := mkKL2 {
  k2_wf : vmwf (vm_maps h);
  k2_nabnd : forall e, In e (vm_noaccess h) -> elo e < ehi e <= 2^64;
  k2_resv : ld_resv L = map wwZ (vm_reserved h);
  k2_resv_img : vm_reserved h = resv_img;
  k2_resv_top : forall e, In e (vm_reserved h) -> ehi e <= bv_unsigned (vm_start_brk h);
  k2_start : 0 < bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_start_brk h) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)
      /\ bv_unsigned (vm_start_brk h) + 4 * PGSZ <= alloc_ceiling
      /\ img_hi <= bv_unsigned (vm_start_brk h);
  k2_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps h) /\ brk_disj L b (mmap_len l);
  k2_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps h) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess h) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  k2_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  k2_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps h) (b + PGSZ) (b + l);
  k2_phase : match ld_brk L with
      | BPUntried => vm_brk h = vm_start_brk h /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk h)
          /\ bv_unsigned (vm_brk h) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk h)
          /\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps h) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk h) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  (* [comment removed for export] *)
  k2_isp : bv_unsigned (vm_init_sp h) = alloc_ceiling + 2 ^ 23 }.

Ltac k2_open HK := destruct HK as [Kwf Kna Kresv Kimg Krt Kstart Kgr Kme Kdis Kreg Kph Kisp].

(* [comment removed for export] *)
Definition phase_inv2 (ph : brk_phase) (L : mled) (pbrk : Z) (h : VmMaps) : Prop :=
  match ph with
  | BPUntried => vm_brk h = vm_start_brk h /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_brk h) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
      /\ (exists e, In e (vm_maps h) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
      /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
  | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk h) = b + l /\ pbrk = b + l
  | BPDead => True
  end.

Lemma KL2_rephase : forall L ph pbrk pbrk' h,
  KL2 L pbrk h -> phase_inv2 ph L pbrk' h -> KL2 (set_brkph ph L) pbrk' h.
Proof. intros L ph pbrk pbrk' h K Hph. k2_open K; constructor; cbn; auto. Qed.

Lemma KL2_dead : forall L pbrk pbrk' h, KL2 L pbrk h -> KL2 (set_brkph BPDead L) pbrk' h.
Proof. intros. eapply KL2_rephase; [eassumption| exact I]. Qed.

Lemma KL2_set_live : forall L v pbrk h, KL2 L pbrk h -> KL2 (set_live v L) pbrk h.
Proof. intros L v pbrk h K. k2_open K; constructor; cbn; auto. Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

Lemma went_In_bounds : forall L pbrk h b l, KL2 L pbrk h ->
  (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
  0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps h)
  /\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
  intros L pbrk h b l K Hin. pose proof alloc_ceiling_lt.
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps h)) as (Hl & Hb & Hc & Hm).
  { destruct Hin as [Hin|[k Hin]]; [pose proof (k2_groups _ _ _ K _ _ Hin)| pose proof (k2_metas _ _ _ K _ _ _ Hin)]; tauto. }
  pose proof (mmap_len_ge l ltac:(lia)). splits; auto; try lia.
  - apply elo_went. lia.
  - apply ehi_went; lia.
Qed.

Lemma In_lranges : forall L x, In x (lranges L) ->
  In x (ld_resv L)
  \/ (exists b l, In (b, l) (ld_groups L) /\ x = (b, round_up_pg l))
  \/ (exists b l k, In (b, l, k) (ld_metas L) /\ x = (b, round_up_pg l))
  \/ (exists b l, ld_brkreg L = Some (b, l) /\ x = (b + PGSZ, round_up_pg l - PGSZ)).
Proof.
  intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
  - left; exact H.
  - right; left. apply in_map_iff in H as ([b l] & <- & H). exists b, l. auto.
  - right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). exists b, l, k. auto.
  - right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. exists b, l. auto.
Qed.

(* [comment removed for export] *)
Lemma KL2_lbrk_pages_ok : forall L pbrk h lo len,
  KL2 L pbrk h ->
  0 < lo -> 0 < len -> lo + len <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
  (forall b l, ld_brkreg L = Some (b, l) -> l mod PGSZ = 0 /\ (b + l <= lo \/ lo + len <= b + PGSZ)) ->
  lbrk_pages_ok L lo len = true.
Proof.
  intros L pbrk h lo len HK Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - rewrite (k2_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.

(* [comment removed for export] *)
Lemma wcov_rf_disj : forall maps lo hi aw nw,
  wcov maps lo hi -> region_free maps aw nw = true -> 0 < bv_unsigned nw -> lo < hi ->
  bv_unsigned aw + bv_unsigned nw <= lo \/ hi <= bv_unsigned aw.
Proof.
  intros maps lo hi aw nw Hc Hrf Hn Hlh.
  destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
  destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
  pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.

Lemma mmap_len_pos_pg : forall l, 0 < l -> PGSZ <= mmap_len l.
Proof.
  intros l Hl. pose proof (mmap_len_ge l Hl). pose proof (mmap_len_aligned l).
  pose proof (Z_div_mod_eq_full (mmap_len l) 4096). unfold PGSZ. nia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KL2_brk0 : forall L pbrk h, KL2 L pbrk h -> ld_brk L = BPUntried ->
  let r := bv_unsigned (vm_brk h) in
  brk0_answer_ok r = true /\ KL2 (set_brkph (BPQueried r) L) r h.
Proof.
  intros L pbrk h HK Hph r.
  pose proof (k2_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  pose proof (bv_unsigned_in_range 64 (vm_brk h)) as R. unfold bv_modulus in R.
  subst r. rewrite Ebrk in *. split.
  - unfold brk0_answer_ok, TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - eapply KL2_rephase; [exact HK|]. cbn [phase_inv2]. rewrite Ebrk. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KL2_mmap_new : forall L pbrk h (a : word) len (isnone : bool),
  KL2 L pbrk h -> brk_quiet L -> 0 < len < LEN_MAX ->
  let n := mmap_len len in
  bv_unsigned a mod PGSZ = 0 -> 0 < bv_unsigned a -> bv_unsigned a + n <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true ->
  let h' := mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
  KL2 (if isnone then set_metas ((bv_unsigned a, len, 0) :: ld_metas L) L else set_groups ((bv_unsigned a, len) :: ld_groups L) L) pbrk h'
  /\ mmap_answer_ok (lranges L) len (bv_unsigned a) = true /\ is_err (bv_unsigned a) = false.
Proof.
  intros L pbrk h aw len isnone HK Hq Hlen n A1 A2 A3 Hrf h'. pose proof alloc_ceiling_lt as Hcl.
  set (a := bv_unsigned aw) in *.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : aw = Z_to_bv 64 a) by (subst a; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (k2_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. unfold PGSZ in A1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - rewrite (k2_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Un in D. exact D.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
      - injection E as -> ->. pose proof (k2_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  k2_open HK.
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            phase_inv2 (ld_brk L') L' pbrk h').
  { intros L' E1 E2. unfold phase_inv2. rewrite E1, E2. subst h'. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  destruct isnone; constructor;
    first [ apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | subst h'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Un; lia| exact Hrfm].
  - intros e [<-|He]; [rewrite elo_pair, ehi_pair, Un; subst a; lia| apply Kna; exact He].
  - intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * left; unfold went, KInv.wz; rewrite <- Ua; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (aw, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Un. fold n in Hq2. subst a. lia.
    + specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - apply vmwf_cons; [exact Kwf| rewrite Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * left; unfold went, KInv.wz; rewrite <- Ua; reflexivity.
      * exact Dbrk.
    + specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KL2_brk_grow1 : forall L pbrk h cur, KL2 L pbrk h -> ld_brk L = BPQueried cur ->
  let b := vm_brk h in
  let req := round_up_pg cur + 2 * PGSZ in
  (* [comment removed for export] *)
  cur = bv_unsigned b /\ pbrk = cur /\ req = bv_unsigned b + 2 * PGSZ /\ bv_unsigned b mod PGSZ = 0 /\ 0 < bv_unsigned b
  /\ bv_unsigned b + 2 * PGSZ < 2 ^ 64 /\ bv_unsigned (vm_start_brk h) <= bv_unsigned b + 2 * PGSZ /\ req <> 0
  (* [comment removed for export] *)
  /\ (answer_ok L (EBrk req) cur = true /\ KL2 (event_post L (EBrk req) cur) cur h)
  (* [comment removed for export] *)
  /\ (region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (2 * PGSZ)) = true -> bv_unsigned b + 2 * PGSZ <= alloc_ceiling ->
      answer_ok L (EBrk req) req = true
      /\ KL2 (event_post L (EBrk req) req) req
             (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 (2 * PGSZ)) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                           (Z_to_bv 64 (bv_unsigned b + 2 * PGSZ)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
Proof.
  intros L pbrk h cur HK Hph b req. pose proof alloc_ceiling_lt as Hcl.
  pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (Ecur & Ebrk & Epbrk & Ereg).
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  pose proof (bv_unsigned_in_range 64 b) as Rb. unfold bv_modulus in Rb.
  assert (Hcb : cur = bv_unsigned b) by (subst b; lia).
  assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
  assert (Hne : req <> 0) by (unfold PGSZ in *; lia).
  assert (Hb2 : bv_unsigned b + 2 * PGSZ < 2 ^ 64) by (rewrite <- Hcb, Ecur; unfold PGSZ in *; lia).
  assert (Hsb : bv_unsigned (vm_start_brk h) <= bv_unsigned b + 2 * PGSZ) by (rewrite <- Hcb, Ecur; unfold PGSZ; lia).
  splits; try lia.
  - rewrite <- Hcb, Ecur. exact S2.
  - (* [comment removed for export] *)
    unfold answer_ok, event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
  - unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    apply KL2_dead with (pbrk := pbrk). exact HK.
  - (* [comment removed for export] *)
    intros Hrf Hceil.
    assert (Hn : bv_unsigned (Z_to_bv 64 (2 * PGSZ)) = 2 * PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
    assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
    { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
      apply (KL2_lbrk_pages_ok L pbrk h cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b1 l1 Hb; rewrite Ereg in Hb; discriminate].
      rewrite Hcb, Z_to_bv_bv_unsigned. exact Hrf. }
    split.
    + unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
      unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Z.eqb_refl, Hph.
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      * apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      * rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      * intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      * intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      * intros b0 l0 Hb. rewrite Ereg in Hb. discriminate.
      * rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        -- exists (b, Z_to_bv 64 (2 * PGSZ)). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
        -- intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
           pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        -- intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
           pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KL2_brk_grow2 : forall L pbrk h b l, KL2 L pbrk h -> ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
  let br := vm_brk h in
  let req := b + l + PGSZ in
  pbrk = b + l /\ bv_unsigned br = b + l /\ req = bv_unsigned br + PGSZ /\ bv_unsigned br mod PGSZ = 0 /\ 0 < bv_unsigned br
  /\ bv_unsigned br + PGSZ < 2 ^ 64 /\ bv_unsigned (vm_start_brk h) <= bv_unsigned br + PGSZ /\ req <> 0
  /\ (answer_ok L (EBrk req) (b + l) = true /\ KL2 (event_post L (EBrk req) (b + l)) (b + l) h)
  /\ (region_free (vm_reserved h ++ vm_maps h) br (Z_to_bv 64 PGSZ) = true -> bv_unsigned br + PGSZ <= alloc_ceiling ->
      answer_ok L (EBrk req) req = true
      /\ KL2 (event_post L (EBrk req) req) req
             (mkVmMapsFull (vm_reserved h) ((br, Z_to_bv 64 PGSZ) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                           (Z_to_bv 64 (bv_unsigned br + PGSZ)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
Proof.
  intros L pbrk h b l HK Hph Ereg br req. pose proof alloc_ceiling_lt as Hcl.
  pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (b' & l' & Ereg' & Ebrk & Epbrk).
  rewrite Ereg in Ereg'. injection Ereg' as <- <-.
  pose proof (k2_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  pose proof (bv_unsigned_in_range 64 br) as Rb. unfold bv_modulus in Rb.
  assert (Hne : req <> 0) by (unfold req, PGSZ in *; lia).
  assert (Hal : bv_unsigned br mod PGSZ = 0).
  { subst br. rewrite Ebrk. unfold PGSZ in *. rewrite Z.add_mod, R2, R4 by lia. reflexivity. }
  splits; try (subst br req; unfold PGSZ in *; lia).
  - unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; unfold req, PGSZ; lia).
    unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
  - unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; unfold req, PGSZ; lia).
    apply KL2_dead with (pbrk := pbrk). exact HK.
  - intros Hrf Hceil. subst br. cbv zeta in *.
    assert (Hn : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
    assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
    { apply (KL2_lbrk_pages_ok L pbrk h (b + l) PGSZ HK); [lia| unfold PGSZ; lia| lia| |].
      - rewrite <- Ebrk, Z_to_bv_bv_unsigned. exact Hrf.
      - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
    split.
    + unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
      unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Z.eqb_refl, Hph, Ereg.
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      * apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      * rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      * intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
      * intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
      * intros b1 l1 E. injection E as <- <-. splits; auto.
        -- clear -R3. unfold PGSZ in *; lia.
        -- unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
        -- clear -Hceil Ebrk. lia.
        -- intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
           ++ destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
           ++ exists (vm_brk h, Z_to_bv 64 PGSZ). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
      * rewrite Hph. exists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_above : forall maps aw nw, (forall e, In e maps -> ehi e <= bv_unsigned aw) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
  replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma KL2_mmap_fixed : forall L pbrk h cur, KL2 L pbrk h -> ld_brk L = BPGuard cur ->
  let a := round_up_pg cur in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  a = cur /\ cur mod PGSZ = 0 /\ 0 < cur /\ cur + PGSZ <= alloc_ceiling
  /\ region_free (vm_reserved h) aw nw = true
  /\ map_contains (vm_maps h) aw nw = true
  /\ mmap_fixed_answer_ok a a = true
  /\ KL2 (event_post L (EMmap a PGSZ PROT_NONE MAPFX) a) pbrk
         (mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
                       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros L pbrk h cur HK Hph a aw nw. pose proof alloc_ceiling_lt as Hcl.
  pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Hrf : region_free (vm_reserved h) aw nw = true).
  { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (k2_resv_top _ _ _ HK). exact He. }
  assert (Hmc : map_contains (vm_maps h) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
  splits.
  - exact Ha.
  - rewrite Ecur. exact S2.
  - lia.
  - unfold PGSZ in *; lia.
  - exact Hrf.
  - exact Hmc.
  - unfold mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
  - unfold event_post. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota.
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
    + intros e [<-|He]; [rewrite elo_pair, ehi_pair, Ua, Un; unfold PGSZ in *; lia|].
      destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
      pose proof (iv_subtract_sub a1 s1 a (a + PGSZ) e ltac:(lia) ltac:(lia) H1'). lia.
    + intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
      specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
      unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
    + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
      specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
      * unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      * intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
        pose proof (Kna _ He) as We.
        destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
                   ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
        exists e'. split; [right; eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
    + intros b1 l1 E. injection E as <- <-. splits.
      * lia.
      * rewrite Ha, Ecur. exact S2.
      * lia.
      * reflexivity.
      * lia.
      * intros z Hz. exists e0. split; [exact He0|]. lia.
    + exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Lemma phase_quiet2 : forall L L' pbrk h h',
  KL2 L pbrk h -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
  vm_start_brk h' = vm_start_brk h -> vm_brk h' = vm_brk h ->
  phase_inv2 (ld_brk L') L' pbrk h'.
Proof.
  intros L L' pbrk h h' HK Hq E1 E2 E3 E4. pose proof (k2_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv2.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

Lemma KL2_munmap : forall L pbrk h a l0 len, KL2 L pbrk h -> brk_quiet L -> In (a, l0) (ld_groups L) ->
  (len = l0 \/ len = round_up_pg l0) ->
  let n := mmap_len l0 in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  0 < len < 2^64 /\ mmap_len len = n /\ a mod PGSZ = 0 /\ 0 < a /\ 0 < n /\ a + n <= alloc_ceiling
  /\ map_has (vm_maps h) aw nw = true
  /\ munmap_answer_ok 0 = true
  /\ KL2 (event_post L (EMunmap a len) 0) pbrk
         (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))
  /\ Z.of_nat (length (map_remove (vm_maps h) aw)) < Z.of_nat (length (vm_maps h))
  /\ live_bytes (map_remove (vm_maps h) aw) <= live_bytes (vm_maps h).
Proof.
  intros L pbrk h a l0 len HK Hq Hin Hlen n aw nw. pose proof alloc_ceiling_lt as Hcl.
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  pose proof (k2_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
  fold n in A4, A5, A6, B2, B5, B6.
  assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
  { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
  destruct Hlen3 as [Hlen1 Hlen2].
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
  assert (Hhas : map_has (vm_maps h) aw nw = true).
  { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  splits; try assumption; try lia.
  - reflexivity.
  - (* [comment removed for export] *)
    unfold event_post. set (L' := set_groups (g_remove a (ld_groups L)) L).
    pose proof (k2_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (k2_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + n) by lia.
    assert (Hph' : phase_inv2 (ld_brk L') L' pbrk
              (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
    { eapply phase_quiet2; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
    { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
    assert (Hkeep : forall e, In e (vm_maps h) -> fst e <> aw -> In e (map_remove (vm_maps h) aw)).
    { intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction. }
    subst L'. k2_open HK. constructor; try exact Hph'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
    + apply vmwf_remove. exact Kwf.
    + intros e He. destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
      pose proof (iv_subtract_sub a1 s1 a (a + n) e ltac:(lia) ltac:(lia) H1'). lia.
    + intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
      apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
    + intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
      * apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
      * intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
        pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D. pose proof (Kna _ He) as We.
        destruct (iv_subtract_contains (fst e) (snd e) a (a + n) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
                   ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
    + rewrite Ezz, map_app, <- app_assoc. exact Kd1.
    + intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
      intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
      intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
      destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
      * rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
      * pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia.
  - (* [comment removed for export] *)
    clear -A5. unfold map_remove. induction (vm_maps h) as [|e es IH]; [destruct A5|]. cbn [List.filter length].
    destruct A5 as [->|Hin'].
    + cbn [fst went]. unfold wz. fold aw. rewrite bv_eqb_refl. cbn [negb]. pose proof (List.filter_length_le (fun p : word * word => negb (bv_eqb (fst p) aw)) es). lia.
    + specialize (IH Hin'). destruct (negb (bv_eqb (fst e) aw)); cbn [length]; lia.
  - apply RefNodes.live_bytes_map_remove_le.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

Lemma KL2_mprotect : forall L pbrk h b l k, KL2 L pbrk h -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
  (2 + k) * PGSZ <= round_up_pg l ->
  let a := b + (1 + k) * PGSZ in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  a mod PGSZ = 0 /\ 0 < a /\ a + PGSZ <= alloc_ceiling
  /\ map_contains (vm_noaccess h) aw nw = true
  /\ map_contains (vm_maps h) aw nw = true
  /\ mprotect_answer_ok 0 = true
  /\ KL2 (event_post L (EMprotect a PGSZ PROT_RW) 0) pbrk
         (mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
                       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros L pbrk h b l k HK Hq Hin Hk2 a aw nw. pose proof alloc_ceiling_lt as Hcl.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  pose proof (k2_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
  pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
  set (nb := mmap_len l) in *.
  assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Hamod : a mod PGSZ = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
  assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
  { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hcm : map_contains (vm_maps h) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
    replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  splits.
  - exact Hamod.
  - lia.
  - lia.
  - exact Hcn.
  - exact Hcm.
  - reflexivity.
  - unfold event_post. cbn [Z.eqb orb]. set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
    pose proof (k2_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (k2_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (Hph' : phase_inv2 (ld_brk L') L' pbrk
              (mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
    { eapply phase_quiet2; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    subst L'. k2_open HK. constructor; try exact Hph'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
    + intros e He. destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
      pose proof (iv_subtract_sub a1 s1 a (a + PGSZ) e ltac:(lia) ltac:(lia) H1'). lia.
    + intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
      specialize (Kme b1 l1 k0 Hin1). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
      unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
      * assert (Eb0 : b0 = b).
        { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
        subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
        splits; try assumption; try lia.
        intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh). pose proof (Kna _ He) as We.
        destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b + q * PGSZ) (b + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
                   ltac:(right; subst a; clear -Hq1; unfold PGSZ in *; nia)) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
      * splits; try assumption.
        intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh). pose proof (Kna _ He) as We.
        assert (D : (b0 + q * PGSZ + PGSZ <= a \/ a + PGSZ <= b0 + q * PGSZ)).
        { destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia. }
        destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh) D) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
    + rewrite map_base_bump. exact Kd.
Qed.

(* [comment removed for export] *)
Lemma KL2_alloc_top : forall L pbrk h, KL2 L pbrk h -> alloc_top h = alloc_ceiling.
Proof. intros L pbrk h HK. unfold alloc_top. rewrite (k2_isp _ _ _ HK), stack_max_size_val. lia. Qed.

Lemma KL2_init_sp_window : forall L pbrk h, KL2 L pbrk h -> sp_window_lo <= bv_unsigned (vm_init_sp h).
Proof. intros L pbrk h HK. rewrite (k2_isp _ _ _ HK). pose_ceil. unfold sp_window_lo. lia. Qed.

End KL2DEF.
End CEIL_WRAP_1.

