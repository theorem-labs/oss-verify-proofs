(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv AllocTop VmKit MmNodes GapGrid.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import RelSpec RefNodes HeapCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. vm_compute. reflexivity. Qed.
Lemma alloc_ceiling_Decode : Decode.alloc_ceiling = alloc_ceiling.
Proof. reflexivity. Qed.
Lemma alloc_ceiling_CEIL_MAX : alloc_ceiling = CEIL_MAX.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma alloc_top_lt : forall h, CEIL_MIN <= alloc_top h <= CEIL_MAX -> 0 < alloc_top h <= alloc_ceiling /\ alloc_top h < 2^47.
Proof. intros h H. unfold CEIL_MIN, CEIL_MAX, alloc_ceiling in *. lia. Qed.
Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq.
  change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  change 4096 with (2^12). Z.div_mod_to_equations. nia.
Qed.
Lemma mmap_len_round_up : forall l, mmap_len l = round_up_pg l.
Proof. intros. unfold mmap_len. symmetry. apply round_up_pg_eq. Qed.
Lemma mmap_len_pgup : forall l, mmap_len l = pgup l.
Proof. reflexivity. Qed.
Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros l Hl. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. Qed.
Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros l. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.
Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l H0 Hm. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. nia. Qed.
Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. rewrite round_up_pg_eq. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. Qed.
Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros x Hx. rewrite round_up_pg_eq. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. nia. Qed.
Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. unfold KInv.wz. rewrite !unsigned_wz by assumption. reflexivity. Qed.
Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

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
Lemma region_free_app_l : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [H1 H]. rewrite H1. cbn. eapply IH. exact H. Qed.

Lemma region_free_InZ : forall maps a n e sz,
  region_free maps a n = true -> In (e, sz) maps ->
  (bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a)%Z.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
  inversion E; subst. unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
  destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma region_free_intro : forall maps a n,
  (forall e sz, In (e, sz) maps -> bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros; apply H; right; assumption).
  specialize (H e0 sz0 (or_introl eq_refl)). unfold iv_overlap.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e0 + bv_unsigned sz0));
  destruct (Z.ltb_spec0 (bv_unsigned e0) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity; lia.
Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_InZ; eauto. Qed.

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

Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
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

Lemma iv_subtract_contains : forall a sz lo hi x y,
  lo < hi ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlh Hax Hxy Hy Hwf Hd. unfold iv_subtract.
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

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi -> bv_unsigned a + bv_unsigned sz <= 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlh Hwf. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, lo < hi -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlh Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; lia| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall a n l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.
Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [app]. rewrite !live_bytes_cons, IH. lia. Qed.
Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [reflexivity|]. rewrite live_bytes_cons. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

(* [comment removed for export] *)
Lemma map_remove_notin : forall maps b, (forall e, In e maps -> fst e <> b) -> map_remove maps b = maps.
Proof.
  induction maps as [|[a n] maps IH]; intros b H; [reflexivity|]. cbn.
  destruct (bv_eqb a b) eqn:E.
  - exfalso. apply bv_eqb_eq in E. exact (H (a, n) (or_introl eq_refl) E).
  - cbn. f_equal. apply IH. intros e He. apply H. right. exact He.
Qed.

Lemma map_remove_split : forall maps b n, vmwf maps -> In (b, n) maps ->
  exists l1 l2, maps = l1 ++ (b, n) :: l2 /\ map_remove maps b = l1 ++ l2.
Proof.
  induction maps as [|[a sz] maps IH]; intros b n WF Hin; [destruct Hin|].
  destruct WF as [Hb Hp]. inversion Hp; subst.
  assert (WF' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  destruct Hin as [E|Hin].
  - inversion E; subst. exists [], maps. split; [reflexivity|].
    change (map_remove ((b, n) :: maps) b) with (if negb (bv_eqb b b) then (b, n) :: map_remove maps b else map_remove maps b).
    rewrite bv_eqb_refl. cbn [negb app].
    apply map_remove_notin. intros e He Ee. pose proof (H1 e He) as D.
    assert (We : elo e < ehi e <= 2^64) by (apply Hb; right; exact He).
    assert (Wb : elo (b, n) < ehi (b, n) <= 2^64) by (apply Hb; left; reflexivity).
    destruct e as [eb en]. cbn in Ee. subst eb. unfold edisj, elo, ehi in *. cbn in *. lia.
  - destruct (IH b n WF' Hin) as (l1 & l2 & -> & Hr). exists ((a, sz) :: l1), l2. split; [reflexivity|].
    change (map_remove ((a, sz) :: l1 ++ (b, n) :: l2) b) with (if negb (bv_eqb a b) then (a, sz) :: map_remove (l1 ++ (b, n) :: l2) b else map_remove (l1 ++ (b, n) :: l2) b).
    destruct (bv_eqb a b) eqn:E; [| cbn [negb app]; rewrite Hr; reflexivity].
    exfalso. apply bv_eqb_eq in E. subst a.
    assert (Hin' : In (b, n) (l1 ++ (b, n) :: l2)) by (apply in_or_app; right; left; reflexivity).
    pose proof (H1 _ Hin') as D.
    assert (We : elo (b, n) < ehi (b, n) <= 2^64) by (apply Hb; right; exact Hin').
    assert (Wb : elo (b, sz) < ehi (b, sz) <= 2^64) by (apply Hb; left; reflexivity).
    unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma live_bytes_remove : forall maps b n, vmwf maps -> In (b, n) maps ->
  live_bytes (map_remove maps b) = live_bytes maps - bv_unsigned n /\ length (map_remove maps b) = (length maps - 1)%nat.
Proof.
  intros maps b n WF Hin. destruct (map_remove_split maps b n WF Hin) as (l1 & l2 & E & Hr). rewrite Hr.
  replace (live_bytes maps) with (live_bytes (l1 ++ (b, n) :: l2)) by (rewrite <- E; reflexivity).
  replace (length maps) with (length (l1 ++ (b, n) :: l2)) by (rewrite <- E; reflexivity).
  rewrite !live_bytes_app, live_bytes_cons, !app_length. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lbrk_bytes (L : mled) : Z :=
  match ld_brk L with
  | BPGuard _ => 2 * PGSZ
  | _ => match ld_brkreg L with Some (_, l) => l | None => 0 end
  end.
Definition lbrk_cnt (L : mled) : Z :=
  match ld_brk L with
  | BPGuard _ => 1
  | _ => match ld_brkreg L with Some (_, l) => l / PGSZ - 1 | None => 0 end
  end.

Definition sum_glen (l : list (Z * Z)) : Z := fold_right (fun g acc => mmap_len (snd g) + acc) 0 l.
Definition sum_mlen (l : list (Z * Z * Z)) : Z := fold_right (fun m acc => mmap_len (snd (fst m)) + acc) 0 l.

(* [comment removed for export] *)
Definition ltotal (L : mled) : Z := sum_glen (ld_groups L) + sum_mlen (ld_metas L) + lbrk_bytes L.
Definition lcount (L : mled) : Z := Z.of_nat (length (ld_groups L)) + Z.of_nat (length (ld_metas L)) + lbrk_cnt L.

Arguments sum_glen l : simpl never.
Arguments sum_mlen l : simpl never.
Lemma sum_glen_cons : forall b l gs, sum_glen ((b, l) :: gs) = mmap_len l + sum_glen gs. Proof. reflexivity. Qed.
Lemma sum_mlen_cons : forall b l k ms, sum_mlen ((b, l, k) :: ms) = mmap_len l + sum_mlen ms. Proof. reflexivity. Qed.
Lemma sum_glen_app : forall l1 l2, sum_glen (l1 ++ l2) = sum_glen l1 + sum_glen l2.
Proof. induction l1 as [|[b l] l1 IH]; intros; [reflexivity|]. cbn [app]. rewrite !sum_glen_cons, IH. lia. Qed.
Lemma sum_mlen_bump : forall a ms, sum_mlen (map (bump_meta a) ms) = sum_mlen ms.
Proof.
  induction ms as [|[[b l] k] ms IH]; intros; [reflexivity|]. cbn [map bump_meta].
  destruct (b + (1 + k) * PGSZ =? a); rewrite !sum_mlen_cons, IH; reflexivity.
Qed.
Lemma length_bump : forall a ms, length (map (bump_meta a) ms) = length ms.
Proof. intros. apply map_length. Qed.

Definition BUDCAP : Z := 2^31.     (* [comment removed for export] *)

(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

(* [comment removed for export] *)
Record KLB (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKLB {
  kb_minv : mminv mo;
  kb_halt : m_halted mo = None;
  kb_wf : vmwf (vm_maps (m_vmmaps mo));
  kb_nawf : forall e, In e (vm_noaccess (m_vmmaps mo)) -> ehi e <= 2^64;
  (* [comment removed for export] *)
  kb_resv : ld_resv L = rband (alloc_top (m_vmmaps mo)) :: map wwZ (vm_reserved (m_vmmaps mo));
  kb_top : CEIL_MIN <= alloc_top (m_vmmaps mo) <= CEIL_MAX;
  kb_hceil : alloc_top (m_vmmaps mo) = hceil;
  kb_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
  kb_resv_wf : forall e, In e (vm_reserved (m_vmmaps mo)) -> elo e < ehi e /\ ehi e - elo e <= 2^34;
  kb_resv_n : (length (vm_reserved (m_vmmaps mo)) <= 8)%nat;
  kb_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_top (m_vmmaps mo);
  kb_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_top (m_vmmaps mo)
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kb_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_top (m_vmmaps mo)
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kb_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kb_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_top (m_vmmaps mo)
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kb_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo)
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  (* [comment removed for export] *)
  kb_live : vm_live_bytes (m_vmmaps mo) = ltotal L;
  kb_count : Z.of_nat (length (vm_maps (m_vmmaps mo))) = lcount L;
  kb_limit : BUDCAP <= vm_limit (m_vmmaps mo) }.

Ltac kb_open K :=
  pose proof (kb_minv _ _ _ K) as Kminv; pose proof (kb_halt _ _ _ K) as Khalt; pose proof (kb_wf _ _ _ K) as Kwf; pose proof (kb_nawf _ _ _ K) as Knwf;
  pose proof (kb_resv _ _ _ K) as Kresv; pose proof (kb_top _ _ _ K) as Ktop; pose proof (kb_hceil _ _ _ K) as Khc; pose proof (kb_resv_top _ _ _ K) as Krtop; pose proof (kb_resv_wf _ _ _ K) as Krwf; pose proof (kb_resv_n _ _ _ K) as Krn;
  pose proof (kb_start _ _ _ K) as Kstart;
  pose proof (kb_groups _ _ _ K) as Kgrp; pose proof (kb_metas _ _ _ K) as Kmet; pose proof (kb_distinct _ _ _ K) as Kdis;
  pose proof (kb_brkreg _ _ _ K) as Kbreg; pose proof (kb_phase _ _ _ K) as Kph;
  pose proof (kb_live _ _ _ K) as Klive; pose proof (kb_count _ _ _ K) as Kcnt; pose proof (kb_limit _ _ _ K) as Klim.

(* [comment removed for export] *)
Lemma KLB_vm_eq : forall L pbrk mo mo',
  KLB L pbrk mo -> mminv mo' -> m_halted mo' = None ->
  m_vmmaps mo' = m_vmmaps mo ->
  KLB L pbrk mo'.
Proof. intros L pbrk mo mo' K MI HH E. kb_open K; constructor; rewrite ?E; auto. Qed.

Lemma KLB_vm_eq' : forall L pbrk mo mo',
  KLB L pbrk mo -> mminv mo' -> m_halted mo' = None ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) ->
  KLB L pbrk mo'.
Proof.
  intros L pbrk mo mo' K MI HH H1 H2 H3 H4 H5 H6 H7. kb_open K; constructor; unfold vm_live_bytes in *; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6, ?H7; auto.
Qed.

Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
  match ph with
  | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo)
      /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
      /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
  | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
  | BPDead => True
  end.

(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m /\ m_stdin m' = m_stdin m
  /\ m_creds m' = m_creds m /\ m_net m' = m_net m.
Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. intros mo. unfold vm_only. repeat split; reflexivity. Qed.
Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof. intros a b c (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). unfold vm_only. repeat split; congruence. Qed.
Lemma vm_only_with_vmmaps : forall h m, vm_only m (with_vmmaps h m).
Proof. intros. unfold vm_only. repeat split; reflexivity. Qed.

Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ev_fixed (flags : Z) : bool := negb (Z.land flags MAP_FIXED_Z =? 0).

(* [comment removed for export] *)
Definition ev_costb (e : ev) : Z :=
  match e with
  | EMmap _ len _ flags => if ev_fixed flags then 0 else mmap_len len
  | EBrk req => if req =? 0 then 0 else 2 * PGSZ
  | _ => 0
  end.
Definition ev_costk (e : ev) : Z :=
  match e with
  | EMmap _ _ _ flags => if ev_fixed flags then 0 else 1
  | EBrk req => if req =? 0 then 0 else 1
  | _ => 0
  end.
(* [comment removed for export] *)
Definition ans_cont (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap _ _ _ flags => if ev_fixed flags then True else is_err z = false
  | EMprotect _ _ _ => z = 0
  | EBrk _ | EMunmap _ _ => True
  | EPeek _ _ _ | EUndef _ => False
  end.

(* [comment removed for export] *)
Fixpoint tbound {R} (t : stree ev Z R) (cb ck : Z) (P : R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k => ev_costb e <= cb /\ ev_costk e <= ck /\
               forall z, ans_cont e z -> tbound (k z) (cb - ev_costb e) (ck - ev_costk e) P
  end.

Lemma tbound_mono {R} : forall (t : stree ev Z R) cb ck cb' ck' (P P' : R -> Prop),
  tbound t cb ck P -> cb <= cb' -> ck <= ck' -> (forall r, P r -> P' r) -> tbound t cb' ck' P'.
Proof.
  induction t as [r|e k IH]; intros cb ck cb' ck' P P' H Hb Hk HP; cbn in *; [auto|].
  destruct H as (H1 & H2 & H3). split; [lia|]. split; [lia|]. intros z Hz. eapply IH; [apply H3; exact Hz| lia| lia| exact HP].
Qed.


(* [comment removed for export] *)
Definition RESV_MAX : Z := 8.
(* [comment removed for export] *)
Definition BUD (L : mled) (mo : Model) (cb ck : Z) : Prop :=
  cb = Z.max 0 (Z.min cb (2^31)) /\ 0 <= ck /\
  ltotal L + cb <= BUDCAP /\ BUDCAP <= vm_limit (m_vmmaps mo) /\
  lcount L + ck + RESV_MAX < GRID_J.

Lemma BUD_cb : forall L mo cb ck, BUD L mo cb ck -> 0 <= cb <= CBMAX.
Proof. intros L mo cb ck (B0 & _). unfold CBMAX. lia. Qed.
Lemma BUD_cb_intro : forall cb, 0 <= cb <= CBMAX -> cb = Z.max 0 (Z.min cb (2^31)).
Proof. intros cb H. unfold CBMAX in H. lia. Qed.

Lemma BUD_mono : forall L mo cb ck cb' ck', BUD L mo cb ck -> 0 <= cb' <= cb -> 0 <= ck' <= ck -> BUD L mo cb' ck'.
Proof. intros L mo cb ck cb' ck' (B0 & B1 & B2 & B3 & B4) Hb Hk. unfold BUD. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_maps_next_noop : forall h req, brk_maps_next h req (vm_brk h) = vm_maps h.
Proof.
  intros h req. unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow.
  rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_unmaps_noop : forall r, brk_unmaps r r = [].
Proof. intros r. unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _); reflexivity. Qed.

Lemma brk_model_next_noop : forall h req,
  let h' := brk_model_next h req (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h /\ vm_limit h' = vm_limit h
  /\ alloc_top h' = alloc_top h.
Proof.
  intros h req. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
  rewrite brk_maps_next_noop, brk_unmaps_noop. cbn. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_next_grown : forall h req,
  let b := bv_unsigned (vm_brk h) in
  0 < b -> b < req < 2^64 ->
  let h' := brk_model_next h (MmNodes.wz req) (MmNodes.wz req) in
  vm_reserved h' = vm_reserved h
  /\ vm_maps h' = (vm_brk h, MmNodes.wz (req - b)) :: vm_maps h
  /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = MmNodes.wz req /\ vm_limit h' = vm_limit h
  /\ alloc_top h' = alloc_top h.
Proof.
  intros h req b Hb Hreq h'. subst h'. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
  unfold brk_maps_next, MmNodes.wz. rewrite unsigned_wz by lia. fold b.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (req <? b) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
  unfold brk_grants, brk_is_grow. rewrite w_is0_wz by lia. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite unsigned_wz by lia. fold b. replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb app].
  unfold brk_unmaps, brk_page_range. rewrite unsigned_wz by lia. fold b.
  replace (page_round_up_Z req <? page_round_up_Z b) with false.
  2:{ symmetry. apply Z.ltb_ge. apply page_round_up_Z_mono. lia. }
  assert (Hsub : (Z_to_bv 64 req - vm_brk h)%bv = Z_to_bv 64 (req - b)).
  { apply bv_eq. rewrite bv_sub_unsigned, unsigned_wz by lia. fold b. rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite Hsub. destruct (0 <? b); cbn; repeat split; reflexivity.
Qed.

Lemma region_free_shrink : forall maps (a n n' : word),
  region_free maps a n = true -> bv_unsigned n' <= bv_unsigned n -> region_free maps a n' = true.
Proof.
  intros maps a n n' H Hle. apply region_free_intro. intros e sz Hin.
  pose proof (region_free_InZ _ _ _ _ _ H Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_facts : forall m req,
  let h := m_vmmaps m in
  let b := bv_unsigned (vm_brk h) in
  0 < b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  brk_grow_ok m (MmNodes.wz req) (MmNodes.wz req) = true ->
  req <= alloc_top h /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true.
Proof.
  intros m req h b Hb Hreq Hba Hra H. unfold brk_grow_ok, MmNodes.wz in H. fold h in H. rewrite unsigned_wz in H by lia. fold b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H by (Z.div_mod_to_equations; nia).
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H by (Z.div_mod_to_equations; nia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
  pose proof (alloc_top_room h) as R. unfold two_pow_64, stack_max_size in R.
  eapply region_free_shrink; [exact H2|]. rewrite !unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState) (cb ck : Z)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ ans_cont e z /\ KLB (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0
                /\ BUD (event_post L e z) mo (cb - ev_costb e) (ck - ev_costk e).

Lemma KLB_rephase : forall L ph pbrk pbrk' mo,
  KLB L pbrk mo -> phase_inv ph L pbrk' mo ->
  lbrk_bytes (set_brkph ph L) = lbrk_bytes L -> lbrk_cnt (set_brkph ph L) = lbrk_cnt L ->
  KLB (set_brkph ph L) pbrk' mo.
Proof.
  intros L ph pbrk pbrk' mo K Hph Hb Hc. kb_open K; constructor; cbn; auto.
  - unfold ltotal in *. cbn. rewrite Hb. exact Klive.
  - unfold lcount in *. cbn. rewrite Hc. exact Kcnt.
Qed.

Lemma lbrk_dead : forall L, brk_quiet L \/ (exists c, ld_brk L = BPQueried c) ->
  lbrk_bytes (set_brkph BPDead L) = lbrk_bytes L /\ lbrk_cnt (set_brkph BPDead L) = lbrk_cnt L.
Proof.
  intros L H. unfold lbrk_bytes, lbrk_cnt, brk_quiet in *. cbn. revert H. destruct (ld_brk L); intros H; try (split; reflexivity).
  destruct H as [[]|[c E]]; discriminate.
Qed.

Lemma mspec_get_bind_eq {A} (s0 : PState) (P : assn PState) (f : PState -> MP A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk0_ok : forall L G s0 cb ck, frame_ok G -> ld_brk L = BPUntried ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
        (ev_step_post L (EBrk 0) G s0 cb ck).
Proof.
  intros L G s0 cb ck HG Hph.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KLB (set_brkph (BPQueried r) L) r mo /\ BUD L mo cb ck)).
    intros s mo (-> & HK & HGs & HB). split; [cbn; lia|].
    intros rsp mo' evs Hst.
    apply (fun X0__ Q1__ => proj1 (nstep_brk_iff mo _ _ _ _ Q1__) X0__) in Hst; [| lia]. destruct Hst as (-> & -> & ->). rewrite !brk_result_query.
    pose proof (kb_minv _ _ _ HK) as MI. rewrite (with_brk_next_eq mo) by exact MI.
    pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz 0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    set (h' := brk_model_next (m_vmmaps mo) (MmNodes.wz 0) (vm_brk (m_vmmaps mo))) in *.
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split.
    { unfold dec_brk0. cbn. unfold brk_zeros, brk_is_grow. change (w_is0 (MmNodes.wz 0)) with true. cbn. rewrite brk_unmaps_noop. reflexivity. }
    assert (HK' : KLB L (ps_brk s0) (with_vmmaps h' mo)).
    { eapply KLB_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)| ..];
        cbn [m_vmmaps with_vmmaps]; unfold m_vmmaps, with_vmmaps; cbn; assumption. }
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Evm : m_vmmaps (with_vmmaps h' mo) = h') by reflexivity.
    pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo))) as R. unfold bv_modulus in R.
    splits.
    - reflexivity.
    - eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
    - unfold brk0_answer_ok. rewrite Ebrk.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KLB_rephase; [exact HK'| | unfold lbrk_bytes; cbn; rewrite Hph; reflexivity| unfold lbrk_cnt; cbn; rewrite Hph; reflexivity].
      cbn [phase_inv]. rewrite Evm, E5, E4, Ebrk. splits; auto.
    - destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD. rewrite Evm, E6. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. intros s mo (s1 & -> & -> & HGs & Hans & HK & HB). unfold ev_step_post. cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb ans_cont ev_costb ev_costk].
  rewrite Z.sub_0_r, Z.sub_0_r.
  splits; auto. { eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs]. }
  destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount in *. cbn. unfold lbrk_bytes, lbrk_cnt in *. cbn. rewrite Hph in B2, B4. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_dec_brk' : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  mminv mo ->
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) < req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\
  ((dec_brk (bv_unsigned (vm_brk h)) req rsp = Some BrkSame /\ mo' = with_vmmaps (brk_model_next h (MmNodes.wz req) (vm_brk h)) mo)
   \/ (dec_brk (bv_unsigned (vm_brk h)) req rsp = Some BrkGrown /\ mo' = with_vmmaps (brk_model_next h (MmNodes.wz req) (MmNodes.wz req)) mo
       /\ brk_grow_ok mo (MmNodes.wz req) (MmNodes.wz req) = true)).
Proof.
  intros req mo rsp mo' evs h MI Hb Hsb Hreq H. assert (R : 0 <= req < 2^64) by lia.
  apply (fun X0__ Q1__ => proj1 (nstep_brk_iff mo _ _ _ _ Q1__) X0__) in H; [|exact R]. destruct H as (-> & -> & ->). split; [reflexivity|].
  rewrite (with_brk_next_eq mo) by exact MI.
  rewrite (brk_result_grow mo (MmNodes.wz req)) by (unfold MmNodes.wz; rewrite ?unsigned_wz by lia; fold h; lia). fold h.
  destruct (brk_grow_ok mo (MmNodes.wz req) (MmNodes.wz req)) eqn:Hgo.
  2: left. 1: right.
  2:{ split; [|reflexivity].
    rewrite brk_unmaps_noop. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r.
    unfold dec_brk. cbn. rewrite Z.eqb_refl. reflexivity. }
  { split; [|auto].
    unfold brk_unmaps, brk_page_range, MmNodes.wz. rewrite unsigned_wz by lia.
    replace (page_round_up_Z req <? page_round_up_Z (bv_unsigned (vm_brk h))) with false
      by (symmetry; apply Z.ltb_ge; apply page_round_up_Z_mono; lia).
    replace (if 0 <? bv_unsigned (vm_brk h) then @nil (word * word) else []) with (@nil (word * word)) by (destruct (0 <? _); reflexivity).
    unfold dec_brk. cbn [no_cc eff_copies eff_copyins]. rewrite unsigned_wz by lia.
    replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [andb]. rewrite Z.eqb_refl.
    unfold brk_zeros, brk_is_grow. rewrite w_is0_wz by lia.
    replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (0 <? bv_unsigned (vm_brk h))%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite unsigned_wz by lia.
    replace (bv_unsigned (vm_brk h) <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [negb andb]. unfold brk_page_range, brk_new_pages, zeros_of, Mem.wa.
    destruct (_ <? _)%Z; rewrite (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity. }
Qed.

Lemma went_In_bounds : forall L pbrk mo b l, KLB L pbrk mo ->
  (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
  0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_top (m_vmmaps mo) /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))
  /\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
  intros L pbrk mo b l K Hin. pose proof alloc_ceiling_lt. pose proof (alloc_top_lt _ (kb_top _ _ _ K)).
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_top (m_vmmaps mo) /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))) as (Hl & Hb & Hc & Hm).
  { destruct Hin as [Hin|[k Hin]]; [pose proof (kb_groups _ _ _ K _ _ Hin)| pose proof (kb_metas _ _ _ K _ _ _ Hin)]; tauto. }
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

Lemma KLB_lbrk_pages_ok : forall L pbrk mo lo len,
  KLB L pbrk mo ->
  let h := m_vmmaps mo in
  0 < lo -> 0 < len -> lo + len <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
  (forall b l, ld_brkreg L = Some (b, l) -> l mod PGSZ = 0 /\ (b + l <= lo \/ lo + len <= b + PGSZ)) ->
  lbrk_pages_ok L lo len = true.
Proof.
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl. pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [Htop _]. fold h in Htop.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - rewrite (kb_resv _ _ _ HK) in H. destruct H as [E|H].
    { unfold rband in E. injection E as <- <-. left. exact Hceil. }
    apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    pose proof (region_free_InZ _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite <- mmap_len_round_up. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite <- mmap_len_round_up. exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.

Lemma with_vmmaps_vmmaps : forall hh m, m_vmmaps (with_vmmaps hh m) = hh.
Proof. reflexivity. Qed.

Lemma ev_brk_grow1_ok : forall L G s0 cur cb ck, frame_ok G -> ld_brk L = BPQueried cur ->
  let req := round_up_pg cur + 2 * PGSZ in
  2 * PGSZ <= cb -> 1 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0 cb ck).
Proof.
  intros L G s0 cur cb ck HG Hph req Hcb Hck. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KLB (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                              /\ BUD (set_brkph (BPGuard cur) L) mo (cb - 2 * PGSZ) (ck - 1)
                | BrkSame => KLB (set_brkph BPDead L) cur mo /\ BUD (set_brkph BPDead L) mo (cb - 2 * PGSZ) (ck - 1)
                end)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    split. { cbn. unfold PGSZ in *. lia. }
    intros rsp mo' evs Hst.
    destruct (nstep_dec_brk' req mo rsp mo' evs MI ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as [-> [[Hdec ->]|(Hdec & -> & Hgo)]].
    - (* [comment removed for export] *)
      exists BrkSame. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz req)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HK' : KLB L cur (with_vmmaps h' mo)).
      { rewrite <- Epbrk. eapply KLB_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)| ..];
          rewrite with_vmmaps_vmmaps; assumption. }
      destruct (lbrk_dead L ltac:(right; eexists; exact Hph)) as [D1 D2].
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + eapply KLB_rephase; [exact HK'| exact I| exact D1| exact D2].
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount in *. rewrite D1, D2. cbn [ld_groups ld_metas set_brkph]. rewrite with_vmmaps_vmmaps, Q6. splits; try lia.
    - (* [comment removed for export] *)
      exists BrkGrown. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      apply brk_grow_ok_facts in Hgo; [| lia| unfold PGSZ in *; lia| rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      pose proof (brk_model_next_grown (m_vmmaps mo) req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KLB_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk (m_vmmaps mo))) at 1 by exact Ebrk.
        replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) by (f_equal; lia). exact Hrf. }
      assert (Hn : bv_unsigned (MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = 2 * PGSZ) by (unfold MmNodes.wz; rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps mo))) as R0. unfold bv_modulus in R0.
      assert (HK' : KLB (set_brkph (BPGuard cur) L) req (with_vmmaps h' mo)).
      { kb_open HK. constructor; rewrite ?with_vmmaps_vmmaps; cbn [set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
          rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7; auto.
        + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; rewrite Z_to_bv_bv_unsigned in Hrf; exact Hrf].
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
        + intros b l Hin. specialize (Kgrp b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
        + intros b l k Hin. specialize (Kmet b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
        + intros b l Hb. rewrite Ereg in Hb. discriminate.
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
          * exists (vm_brk (m_vmmaps mo), MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
          * intros b l Hin. pose proof (went_In_bounds _ _ _ b l HK (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
            rewrite Z_to_bv_bv_unsigned in Hrf.
            pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
          * intros b l k Hin. pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
            rewrite Z_to_bv_bv_unsigned in Hrf.
            pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        + unfold vm_live_bytes in *. subst h'. rewrite P2, live_bytes_cons, Hn, Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg set_brkph ld_groups ld_metas]. rewrite Hph, Ereg. lia.
        + cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg set_brkph ld_groups ld_metas]. rewrite Hph, Ereg. lia. }
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *. cbn. rewrite Hph, Ereg in B2, B4.
        rewrite with_vmmaps_vmmaps, P6. splits; try lia. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & (HK & HPG & HB)). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK & HB). unfold ev_step_post.
    cbn [answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma ev_brk_grow2_ok : forall L G s0 b l cb ck, frame_ok G -> ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
  let req := b + l + PGSZ in
  2 * PGSZ <= cb -> 1 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0 cb ck).
Proof.
  intros L G s0 b l cb ck HG Hph Ereg req Hcb Hck. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KLB (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                              /\ BUD (set_brkreg (Some (b, l + PGSZ)) L) mo (cb - 2 * PGSZ) (ck - 1)
                | BrkSame => KLB (set_brkph BPDead L) (b + l) mo /\ BUD (set_brkph BPDead L) mo (cb - 2 * PGSZ) (ck - 1)
                end)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (kb_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    split. { cbn. unfold PGSZ in *. lia. }
    intros rsp mo' evs Hst.
    destruct (nstep_dec_brk' req mo rsp mo' evs MI ltac:((first [clear - S3 S1; lia | lia])) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as [-> [[Hdec ->]|(Hdec & -> & Hgo)]].
    - (* [comment removed for export] *)
      exists BrkSame. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz req)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HK' : KLB L (b + l) (with_vmmaps h' mo)).
      { rewrite <- Epbrk. eapply KLB_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)| ..];
          rewrite with_vmmaps_vmmaps; assumption. }
      destruct (lbrk_dead L ltac:(left; unfold brk_quiet; rewrite Hph; exact I)) as [D1 D2].
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + eapply KLB_rephase; [exact HK'| exact I| exact D1| exact D2].
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount in *. rewrite D1, D2. cbn [ld_groups ld_metas set_brkph]. rewrite with_vmmaps_vmmaps, Q6. splits; try (first [clear - Hcb Hck S2 B2 B3 B4; lia | lia]).
    - (* [comment removed for export] *)
      exists BrkGrown. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      apply brk_grow_ok_facts in Hgo; [| (first [clear - S3 S1; lia | lia])| unfold PGSZ in *; lia| rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      pose proof (brk_model_next_grown (m_vmmaps mo) req ltac:((first [clear - S3 S1; lia | lia])) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KLB_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [(first [clear - R4 R3 R1; lia | lia])| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk (m_vmmaps mo))) at 1 by exact Ebrk.
          replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) by (f_equal; (first [clear - Ebrk; lia | lia])). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      assert (Hn : bv_unsigned (MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = PGSZ) by (unfold MmNodes.wz; rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps mo))) as R0. unfold bv_modulus in R0.
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (HK' : KLB (set_brkreg (Some (b, l + PGSZ)) L) req (with_vmmaps h' mo)).
      { kb_open HK. constructor; rewrite ?with_vmmaps_vmmaps; cbn [set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
          rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7; auto.
        + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try (first [clear - Kstart Ebrk; lia | lia]); auto.
        + intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
          specialize (Kgrp b0 l0 Hin). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
          unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
        + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
          specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
          unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
        + intros b1 l1 E. injection E as <- <-. splits; auto.
          * clear -R3. unfold PGSZ in *; lia.
          * unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
          * clear -Hceil. subst req. lia.
          * intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
            -- destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
            -- exists (vm_brk (m_vmmaps mo), MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. (first [clear - Hge Hx Ebrk; lia | lia]).
        + rewrite Hph. exists b, (l + PGSZ). unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; (first [clear; lia | lia]).
        + unfold vm_live_bytes in *. subst h'. rewrite P2, live_bytes_cons, Hn, Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas]. rewrite Hph, Ereg. lia.
        + cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas]. rewrite Hph, Ereg.
          unfold PGSZ in *. replace (l + 4096) with (l + 1 * 4096) by lia. rewrite Z.div_add by lia. lia. }
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas] in *. rewrite Hph, Ereg in B2, B4. rewrite Hph.
        rewrite with_vmmaps_vmmaps, P6. unfold PGSZ in *. replace (l + 4096) with (l + 1 * 4096) by lia. rewrite Z.div_add by lia. splits; try lia. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & (HK & HPG & HB)). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK & HB). unfold ev_step_post.
    cbn [answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
  intros l Hl. pose proof (mmap_len_ge l Hl). pose proof (mmap_len_aligned l). unfold PGSZ. Z.div_mod_to_equations. nia.
Qed.

Lemma KLB_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
  KLB L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  a mod 4096 = 0 -> 0 < a -> a + n <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  mminv mo' -> m_halted mo' = None ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KLB (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n A1 A2 A3 Hrf Hmi' Hh' Evm. pose proof alloc_ceiling_lt as Hcl.
  pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47]. fold h in Htop0, HtopC, Htop47.
  assert (Etop : alloc_top (m_vmmaps mo') = alloc_top h) by (rewrite Evm; apply alloc_top_same_sp).
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; symmetry; apply mmap_len_round_up).
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kb_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ alloc_ceiling)) by lia. cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - rewrite (kb_resv _ _ _ HK) in H. destruct H as [E|H].
        { unfold rband in E. injection E as <- <-. left. exact A3. }
        apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        pose proof (region_free_InZ _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ua, Un in D. exact D.
      - injection E as -> ->. rewrite <- mmap_len_round_up. apply Dgm. left; exact H.
      - injection E as -> ->. rewrite <- mmap_len_round_up. apply Dgm. right; exists k; exact H.
      - injection E as -> ->. pose proof (kb_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  kb_open HK.
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            match ld_brk L' with
            | BPUntried => vm_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo') /\ ld_brkreg L' = None
            | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo')) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur /\ pbrk = cur /\ ld_brkreg L' = None
            | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo'))
                /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
                /\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo')
                /\ (exists e, In e (vm_maps (m_vmmaps mo')) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
                /\ (forall b l, In (b, l) (ld_groups L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
                /\ (forall b l k, In (b, l, k) (ld_metas L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
            | BPLive => exists b l, ld_brkreg L' = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = b + l /\ pbrk = b + l
            | BPDead => True
            end).
  { intros L' E1 E2. rewrite E1, E2, Etop, Evm. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  assert (Hlbb : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L -> lbrk_bytes L' = lbrk_bytes L /\ lbrk_cnt L' = lbrk_cnt L).
  { intros L' E1 E2. unfold lbrk_bytes, lbrk_cnt. rewrite E1, E2. split; reflexivity. }
  destruct isnone; constructor;
    first [ apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | rewrite ?Etop, ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros e [<-|He]; [rewrite ehi_pair, Ua, Un; lia| apply Knwf; exact He].
  - intros b0 l0 Hin. specialize (Kgrp b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try (first [clear - Hlen A2 A3 Hn2; lia | lia]).
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. lia.
    + specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kbreg b0 l0 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - unfold vm_live_bytes in *. rewrite live_bytes_cons, Un, Klive. unfold ltotal. cbn [ld_groups ld_metas set_metas]. rewrite sum_mlen_cons.
    destruct (Hlbb (set_metas ((a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [-> _]. fold n. lia.
  - cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount. cbn [ld_groups ld_metas set_metas length].
    destruct (Hlbb (set_metas ((a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [_ ->]. lia.
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
    + specialize (Kgrp b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kbreg b0 l0 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - unfold vm_live_bytes in *. rewrite live_bytes_cons, Un, Klive. unfold ltotal. cbn [ld_groups ld_metas set_groups]. rewrite sum_glen_cons.
    destruct (Hlbb (set_groups ((a, len) :: ld_groups L) L) eq_refl eq_refl) as [-> _]. fold n. lia.
  - cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount. cbn [ld_groups ld_metas set_groups length].
    destruct (Hlbb (set_groups ((a, len) :: ld_groups L) L) eq_refl eq_refl) as [_ ->]. lia.
Qed.

Lemma is_errno_form_neg : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
Lemma is_err_neg : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

Lemma live_bytes_In_le : forall maps e, In e maps -> bv_unsigned (snd e) <= live_bytes maps.
Proof.
  induction maps as [|[a n] maps IH]; intros e Hin; [destruct Hin|]. rewrite live_bytes_cons.
  pose proof (live_bytes_nonneg maps). pose proof (bv_unsigned_in_range 64 n).
  destruct Hin as [<-|Hin]; [cbn; lia|]. specialize (IH e Hin). lia.
Qed.

Lemma mmap_addr_ok_intro : forall len (a : word), bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + mmap_len len <= hceil -> mmap_addr_ok len [] (bv_unsigned a) = true.
Proof.
  intros len a H1 H2 H3. unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2).
  rewrite (proj2 (Z.leb_le _ _) H3). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BUD_gap : forall L pbrk mo nZ cb ck,
  KLB L pbrk mo -> BUD L mo cb ck -> 0 < nZ <= cb -> nZ mod 4096 = 0 -> 1 <= ck ->
  (exists a, mmap_grant_conds mo a nZ) /\ vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros L pbrk mo nZ cb ck HK (B0 & B1 & B2 & B3 & B4) HnZ Hal Hck. kb_open HK.
  pose proof (vm_backing_used_le_live' mo Kminv) as VB.
  pose proof (live_bytes_nonneg (vm_maps (m_vmmaps mo))) as LN. unfold vm_live_bytes, BUDCAP, GRID_W in *.
  split; [| lia].
  destruct (gap_exists (m_vmmaps mo) nZ) as (a & C1 & C2 & C3 & C4); [unfold CBMAX in *; lia| exact Hal| | | | | unfold CEIL_MIN in *; lia|].
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [apply Krwf; exact Hin|].
    destruct Kwf as [Hb _]. specialize (Hb e Hin). pose proof (live_bytes_In_le _ _ Hin). unfold elo, ehi, GRID_W in *. lia.
  - unfold GRID_RESV. lia.
  - rewrite Kcnt. unfold RESV_MAX in B4. lia.
  - unfold GRID_W. lia.
  - exists a. unfold mmap_grant_conds, MmNodes.wz. cbv zeta. auto.
Qed.

Lemma ev_mmap_core : forall L G s0 len (isnone : bool) cb ck, frame_ok G -> brk_quiet L -> 0 < len < LEN_MAX ->
  mmap_len len <= cb -> 1 <= ck ->
  let prot := if isnone then PROT_NONE else PROT_RW in
  let dec := if isnone then dec_mmap_none len [] else dec_mmap len [] in
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (a <- msys (NMmap 0 len prot MAPF) dec ;; mret match a with MmErr e => neg_errno e | MmOk x => x end)
        (ev_step_post L (EMmap 0 len prot MAPF) G s0 cb ck).
Proof.
  intros L G s0 len isnone cb ck HG Hq Hlen Hcb Hck prot dec.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_aligned len) as Hna.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMmap 0 len prot MAPF) dec _
             (fun x s mo => s = s0 /\ G s mo /\
                match x with
                | MmErr e => False
                | MmOk a => KLB (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) (ps_brk s0) mo
                            /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false
                            /\ BUD (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) mo (cb - mmap_len len) (ck - 1)
                end)).
    intros s mo (-> & HK & HGs & HB). pose proof HB as (B0 & B1 & B2 & B3 & B4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47]. pose proof (kb_hceil _ _ _ HK) as Khc.
    pose proof (kb_live _ _ _ HK) as Klive. pose proof (live_bytes_nonneg (vm_maps (m_vmmaps mo))) as LN. unfold vm_live_bytes in Klive.
    assert (Hl62 : 0 < len < 2^62) by (unfold BUDCAP in *; lia).
    split. { cbn. left. subst prot. destruct isnone; splits; auto; lia. }
    destruct (BUD_gap L (ps_brk s0) mo (mmap_len len) cb ck HK HB ltac:(lia) Hna Hck) as [GAP BK].
    intros rsp mo' evs Hst.
    assert (Hcase : exists a, mmap_grant_conds mo a (mmap_len len) /\ dec rsp = Some (MmOk (bv_unsigned a)) /\
              mo' = (if isnone then mmap_na_model mo a (mmap_len len) else mmap_rw_model mo a (mmap_len len))).
    { subst prot dec. destruct isnone.
      - apply (fun X0__ Q1__ => proj1 (nstep_mmap_na_iff mo _ _ _ _ Q1__) X0__) in Hst; [|exact Hl62]. destruct Hst as (_ & [(_ & _ & NOGAP)|(a & C & -> & ->)]).
        + exfalso. apply NOGAP. exact GAP.
        + exists a. split; [exact C|]. split; [|reflexivity]. destruct C as (C1 & C2 & C3 & C4).
          unfold dec_mmap_none. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite !bv_eqb_refl. cbn [andb].
          rewrite mmap_addr_ok_intro; auto. cbv zeta in C3. change (pgup len) with (mmap_len len) in C3. lia.
      - apply (fun X0__ Q1__ => proj1 (nstep_mmap_rw_iff mo _ _ _ _ Q1__) X0__) in Hst; [|exact Hl62]. destruct Hst as (_ & [(_ & _ & NOGAP)|(a & C & _ & -> & ->)]).
        + exfalso. apply NOGAP. destruct GAP as (a & Ha). exists a. split; [exact Ha| exact BK].
        + exists a. split; [exact C|]. split; [|reflexivity]. destruct C as (C1 & C2 & C3 & C4).
          unfold dec_mmap. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite !bv_eqb_refl. cbn [andb].
          rewrite mmap_addr_ok_intro; auto. cbv zeta in C3. change (pgup len) with (mmap_len len) in C3. lia. }
    destruct Hcase as (a & (C1 & C2 & C3 & C4) & Hd & Emo'). exists (MmOk (bv_unsigned a)). split; [exact Hd|].
    assert (VO : vm_only mo mo') by (rewrite Emo'; destruct isnone; apply vm_only_with_vmmaps).
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact VO| exact HGs]|].
    assert (MI' : mminv mo') by (rewrite Emo'; destruct isnone; apply mminv_with_vmmaps; exact MI).
    assert (HH' : m_halted mo' = None) by (rewrite Emo'; destruct isnone; rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)).
    assert (Evm : m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                 (if isnone then (Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                 (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))).
    { rewrite Emo', Z_to_bv_bv_unsigned. destruct isnone; reflexivity. }
    destruct (KLB_mmap_new L (ps_brk s0) mo mo' (bv_unsigned a) len isnone HK Hq Hlen
                ltac:(rewrite page_size_eq in C1; exact C1) C2 C3
                ltac:(rewrite Z_to_bv_bv_unsigned; exact C4) MI' HH' Evm) as (HK' & Hans & Herr).
    splits; auto.
    unfold BUD. assert (Elim : vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo)) by (rewrite Evm; reflexivity). rewrite Elim.
    unfold ltotal, lcount in *.
    assert (Hlbb : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L -> lbrk_bytes L' = lbrk_bytes L /\ lbrk_cnt L' = lbrk_cnt L).
    { intros L' E1 E2. unfold lbrk_bytes, lbrk_cnt. rewrite E1, E2. split; reflexivity. }
    destruct isnone; cbn [ld_groups ld_metas set_metas set_groups length];
      [destruct (Hlbb (set_metas ((bv_unsigned a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [-> ->]; rewrite sum_mlen_cons
      |destruct (Hlbb (set_groups ((bv_unsigned a, len) :: ld_groups L) L) eq_refl eq_refl) as [-> ->]; rewrite sum_glen_cons];
      rewrite Nat2Z.inj_succ; splits; lia. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & Hx). unfold ev_step_post, ans_cont, ev_costb, ev_costk, ev_fixed.
  cbn [answer_ok event_post]. change (Z.land MAPF MAP_FIXED_Z =? 0) with true. change (Z.land MAPF MAP_FIXED =? 0) with true. cbn [negb]. cbv iota.
  destruct x as [e|a]; [destruct Hx|].
  destruct Hx as (HK & Hans & Herr & HB). rewrite Herr. subst prot. destruct isnone.
  + change (PROT_NONE =? PROT_NONE) with true. cbv iota. splits; auto.
  + change (PROT_RW =? PROT_NONE) with false. cbv iota. splits; auto.
Qed.

Lemma ev_mmap_ok : forall L G s0 len prot cb ck, frame_ok G -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX ->
  mmap_len len <= cb -> 1 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (ev_step (EMmap 0 len prot MAPF))
        (ev_step_post L (EMmap 0 len prot MAPF) G s0 cb ck).
Proof.
  intros L G s0 len prot cb ck HG Hq Hprot Hlen Hcb Hck. unfold ev_step.
  change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hprot as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core L G s0 len true cb ck HG Hq Hlen Hcb Hck).
  - change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core L G s0 len false cb ck HG Hq Hlen Hcb Hck).
Qed.
End HC.
