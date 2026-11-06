From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel CheckRep drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotRI3 SlotNcWt ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import StatementKept SlotInv SlotSteps
  HarnessRep RelayRep gestures_end_b_c relay_add_b_c op_add_c SlotMove.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition p2_same (a n a' n' : Z) : bool := (a' =? a) && (n' =? n).

Definition p2_bnc (e : rentry) : list Z := if re_cap e =? 0 then [] else [re_buf e].

Definition p2_hnc (e : rentry) : list Z := if re_hp e =? 0 then [] else [re_hp e].

Definition p2_buf_dels (e e' : rentry) : list (Z * Z) :=
  if p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e') || (re_cap e =? 0) then [] else [(re_buf e, re_cap e)].

Definition p2_buf_adds (e e' : rentry) : list (Z * Z) :=
  if p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e') || (re_cap e' =? 0) then [] else [(re_buf e', re_cap e')].

Definition p2_hp_dels (e e' : rentry) : list (Z * Z) :=
  if p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e') || (re_hp e =? 0) then [] else [(re_hp e, re_kh e)].

Definition p2_hp_adds (e e' : rentry) : list (Z * Z) :=
  if p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e') || (re_hp e' =? 0) then [] else [(re_hp e', re_kh e')].

Definition p2_arr_dels (l l' : hlist) : list (Z * Z) :=
  if p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l') then [] else arr_sz l.

Definition p2_arr_adds (l l' : hlist) : list (Z * Z) :=
  if p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l') then [] else arr_sz l'.

Definition p2_dr_dels (out CAP q1 CAP' : Z) (e e' : rentry) (x x' : hlist) : list (Z * Z) :=
  out_move_dels out CAP q1 CAP' ++ p2_buf_dels e e' ++ p2_hp_dels e e' ++ p2_arr_dels x x'.

Definition p2_dr_adds (out CAP q1 CAP' : Z) (e e' : rentry) (x x' : hlist) : list (Z * Z) :=
  out_move_adds out CAP q1 CAP' ++ p2_buf_adds e e' ++ p2_hp_adds e e' ++ p2_arr_adds x x'.

Definition p2_oR (out CAP q1 CAP' : Z) : list Z := if out_same out CAP q1 CAP' then [out] else [].

Definition p2_gone (out CAP q1 CAP' : Z) : list Z :=
  if out_same out CAP q1 CAP' then [] else if CAP =? 0 then [out] else [].

Definition p2_bR (e e' : rentry) : list Z :=
  if p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e') then p2_bnc e else [].

Definition p2_hR (e e' : rentry) : list Z :=
  if p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e') then p2_hnc e else [].

Definition p2_xR (l l' : hlist) : list Z :=
  if p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l') then arr_nc l else [].

Definition p2_srecs (h : hsrc) : list Z :=
  map fst (hl_recs (hs_pending h)) ++ map fst (hl_recs (hs_expected h)) ++ map fst (hl_recs (hs_held h)).

Definition p2_rest (es : list rentry) (hj : list (hsrc * nat)) : list Z :=
  concat (map (fun e => map key_addr (re_keys e)) es) ++ concat (map (fun p => p2_srecs (fst p)) hj).

Definition p2_one (a x : Z) : nat := if Z.eq_dec a x then 1%nat else 0%nat.

Lemma p2_cnt_cons : forall a l x, count_occ Z.eq_dec (a :: l) x = (p2_one a x + count_occ Z.eq_dec l x)%nat.
Proof. intros a l x. cbn [count_occ]. unfold p2_one. destruct (Z.eq_dec a x); reflexivity. Qed.

Lemma p2_cnt_nil : forall x, count_occ Z.eq_dec [] x = 0%nat.
Proof. reflexivity. Qed.

Ltac p2_cr := repeat first [rewrite count_occ_app | rewrite p2_cnt_cons | rewrite p2_cnt_nil].

Ltac p2_crh H := repeat first [rewrite count_occ_app in H | rewrite p2_cnt_cons in H | rewrite p2_cnt_nil in H].

Lemma p2_cnt : forall (l l' : list Z), Permutation l l' -> forall x, count_occ Z.eq_dec l x = count_occ Z.eq_dec l' x.
Proof. intros l l' H. exact (proj1 (Permutation_count_occ Z.eq_dec l l') H). Qed.

Lemma p2_perm : forall (l l' : list Z), (forall x, count_occ Z.eq_dec l x = count_occ Z.eq_dec l' x) -> Permutation l l'.
Proof. intros l l' H. exact (proj2 (Permutation_count_occ Z.eq_dec l l') H). Qed.

Lemma p2_same_eq : forall a n a' n', p2_same a n a' n' = true -> a' = a /\ n' = n.
Proof. intros a n a' n' H. unfold p2_same in H. apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1, H2. tauto. Qed.

Lemma p2_enc : forall e, entry_nc e = p2_bnc e ++ p2_hnc e.
Proof. reflexivity. Qed.

Lemma p2_snc : forall h,
  src_nc h = arr_nc (hs_pending h) ++ [hs_partial h] ++ arr_nc (hs_expected h) ++ arr_nc (hs_held h).
Proof. reflexivity. Qed.

Lemma p2_arr_fst : forall l, map fst (arr_sz l) = arr_nc l.
Proof. intros l. unfold arr_sz, arr_nc. destruct (hl_cap l =? 0); reflexivity. Qed.

Lemma p2_out_pd : forall out CAP q1 CAP',
  Permutation [out] (p2_oR out CAP q1 CAP' ++ map fst (out_move_dels out CAP q1 CAP') ++ p2_gone out CAP q1 CAP').
Proof.
  intros out CAP q1 CAP'. unfold p2_oR, out_move_dels, p2_gone.
  destruct (out_same out CAP q1 CAP'); cbn [orb]; [apply Permutation_refl|].
  destruct (CAP =? 0); apply Permutation_refl.
Qed.

Lemma p2_out_pa : forall out CAP q1 CAP',
  Permutation [q1] (p2_oR out CAP q1 CAP' ++ map fst (out_move_adds out CAP q1 CAP')).
Proof.
  intros out CAP q1 CAP'. unfold p2_oR, out_move_adds. destruct (out_same out CAP q1 CAP') eqn:S.
  - unfold out_same in S. apply andb_true_iff in S as [S _]. apply Z.eqb_eq in S. subst q1. apply Permutation_refl.
  - apply Permutation_refl.
Qed.

Lemma p2_buf_pd : forall e e', Permutation (p2_bnc e) (p2_bR e e' ++ map fst (p2_buf_dels e e')).
Proof.
  intros e e'. unfold p2_bR, p2_buf_dels, p2_bnc.
  destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e')); cbn [orb].
  - cbn [map]. rewrite app_nil_r. apply Permutation_refl.
  - destruct (re_cap e =? 0); apply Permutation_refl.
Qed.

Lemma p2_buf_pa : forall e e', Permutation (p2_bnc e') (p2_bR e e' ++ map fst (p2_buf_adds e e')).
Proof.
  intros e e'. unfold p2_bR, p2_buf_adds. destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e')) eqn:S; cbn [orb].
  - apply p2_same_eq in S as [S1 S2]. unfold p2_bnc. rewrite S1, S2. cbn [map]. rewrite app_nil_r. apply Permutation_refl.
  - unfold p2_bnc. destruct (re_cap e' =? 0); apply Permutation_refl.
Qed.

Lemma p2_hp_pd : forall e e', Permutation (p2_hnc e) (p2_hR e e' ++ map fst (p2_hp_dels e e')).
Proof.
  intros e e'. unfold p2_hR, p2_hp_dels, p2_hnc.
  destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e')); cbn [orb].
  - cbn [map]. rewrite app_nil_r. apply Permutation_refl.
  - destruct (re_hp e =? 0); apply Permutation_refl.
Qed.

Lemma p2_hp_pa : forall e e', Permutation (p2_hnc e') (p2_hR e e' ++ map fst (p2_hp_adds e e')).
Proof.
  intros e e'. unfold p2_hR, p2_hp_adds. destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e')) eqn:S; cbn [orb].
  - apply p2_same_eq in S as [S1 S2]. unfold p2_hnc. rewrite S1. cbn [map]. rewrite app_nil_r. apply Permutation_refl.
  - unfold p2_hnc. destruct (re_hp e' =? 0); apply Permutation_refl.
Qed.

Lemma p2_arr_pd : forall l l', Permutation (arr_nc l) (p2_xR l l' ++ map fst (p2_arr_dels l l')).
Proof.
  intros l l'. unfold p2_xR, p2_arr_dels. destruct (p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l')).
  - cbn [map]. rewrite app_nil_r. apply Permutation_refl.
  - rewrite p2_arr_fst. apply Permutation_refl.
Qed.

Lemma p2_arr_pa : forall l l', Permutation (arr_nc l') (p2_xR l l' ++ map fst (p2_arr_adds l l')).
Proof.
  intros l l'. unfold p2_xR, p2_arr_adds. destruct (p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l')) eqn:S.
  - apply p2_same_eq in S as [S1 S2]. unfold arr_nc. rewrite S1, S2. cbn [map]. rewrite app_nil_r. apply Permutation_refl.
  - rewrite p2_arr_fst. apply Permutation_refl.
Qed.

Definition p2_pin (t : Z * Z) (l : list (Z * Z)) : bool := existsb (fun u => (fst u =? fst t) && (snd u =? snd t)) l.

Lemma p2_pin_spec : forall t l, p2_pin t l = true <-> In t l.
Proof.
  intros [a m] l. unfold p2_pin. rewrite existsb_exists. split.
  - intros ([b k] & H & E). apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
    cbn [fst snd] in E1, E2. subst b k. exact H.
  - intros H. exists (a, m). split; [exact H|]. cbn [fst snd]. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma p2_nd_disj : forall (l1 l2 : list Z), List.NoDup (l1 ++ l2) -> forall x, In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 H x H1 H2; [destruct H1|].
  cbn [app] in H. apply NoDup_cons_iff in H as [Hy H]. destruct H1 as [<-|H1].
  - apply Hy. apply in_or_app. right. exact H2.
  - exact (IH l2 H x H1 H2).
Qed.

Lemma p2_mv : forall (V V' : rview) (L : layout) (A : astate) (L' : layout) (A' : astate)
    (dels adds : list (Z * Z)) (R gone : list Z),
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  List.NoDup (rv_nc V) -> List.NoDup (rv_nc V') ->
  Permutation (rv_nc V) (R ++ map fst dels ++ gone) -> Permutation (rv_nc V') (R ++ map fst adds) ->
  incl dels (blocks L A) -> incl adds (blocks L' A') ->
  (forall x m, In (x, m) (blocks L A) -> In x R -> In (x, m) (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 <= m) -> (forall q m, In (q, m) (blocks L' A') -> 0 <= m) ->
  (forall g, In g gone -> forall m, ~ In (g, m) (blocks L A)) ->
  nc_move V L A V' L' A' dels adds.
Proof.
  intros V V' L A L' A' dels adds R gone ND0 ND1 NV NV' PV PV' ID IA KR P0 P1 Gn.
  pose proof (Permutation_NoDup PV NV) as NR. pose proof (Permutation_NoDup PV' NV') as NR'.
  assert (NDd : List.NoDup (map fst dels)) by exact (NoDup_app_remove_r _ _ (NoDup_app_remove_l _ _ NR)).
  assert (NDa : List.NoDup (map fst adds)) by exact (NoDup_app_remove_l _ _ NR').
  assert (RD : forall x, In x R -> ~ In x (map fst dels)).
  { intros x Hx Hd. apply (p2_nd_disj R (map fst dels ++ gone) NR x Hx). apply in_or_app. left. exact Hd. }
  assert (RA : forall x, In x R -> ~ In x (map fst adds)) by exact (p2_nd_disj R (map fst adds) NR').
  set (keep := fun x => negb (existsb (Z.eqb x) (map fst dels)) && negb (existsb (Z.eqb x) (map fst adds)) &&
                        existsb (fun t => (fst t =? x) && p2_pin t (blocks L' A')) (blocks L A)).
  set (X := filter (fun t => negb (p2_pin t adds) && negb (keep (fst t) && p2_pin t (blocks L A))) (blocks L' A')).
  apply (mv_build V V' L A L' A' dels adds X R gone keep ND0 ND1 PV PV' ID NDd).
  - intros t Ht. unfold keep. rewrite (mv_negb_in (fst t) (map fst dels) (in_map fst _ _ Ht)). reflexivity.
  - intros x m Hx Hk HR. unfold keep in Hk.
    rewrite (mv_negb_nin x _ (RD x HR)), (mv_negb_nin x _ (RA x HR)) in Hk. cbn [andb] in Hk.
    assert (E : existsb (fun t => (fst t =? x) && p2_pin t (blocks L' A')) (blocks L A) = true).
    { apply existsb_exists. exists (x, m). split; [exact Hx|]. cbn [fst]. rewrite Z.eqb_refl. cbn [andb].
      apply p2_pin_spec. exact (KR x m Hx HR). }
    rewrite E in Hk. discriminate.
  - intros x m Hx. destruct (p2_pin (x, m) adds) eqn:Pa.
    + right. apply in_or_app. left. apply p2_pin_spec. exact Pa.
    + destruct (keep x && p2_pin (x, m) (blocks L A)) eqn:Kp.
      * left. apply andb_true_iff in Kp as [K1 K2]. split; [apply p2_pin_spec; exact K2|exact K1].
      * right. apply in_or_app. right. unfold X. apply filter_In. split; [exact Hx|]. cbn [fst]. rewrite Pa, Kp.
        reflexivity.
  - intros x m Hx Hk. unfold keep in Hk. apply andb_true_iff in Hk as [_ Hk].
    apply existsb_exists in Hk as ([y k] & Hy & Hk). apply andb_true_iff in Hk as [Hy1 Hy2].
    apply Z.eqb_eq in Hy1. cbn [fst] in Hy1. subst y. apply p2_pin_spec in Hy2.
    rewrite (mv_fst_uniq (blocks L A) x m k ND0 Hx Hy). exact Hy2.
  - intros t Ht. apply in_app_or in Ht as [Ht|Ht]; [exact (IA t Ht)|]. unfold X in Ht. apply filter_In in Ht.
    exact (proj1 Ht).
  - apply mv_nodup_app.
    + exact (NoDup_map_inv _ _ NDa).
    + unfold X. apply NoDup_filter. exact (NoDup_map_inv _ _ ND1).
    + intros t Ht Hx. unfold X in Hx. apply filter_In in Hx as [_ Hx]. apply andb_true_iff in Hx as [Hx _].
      rewrite (proj2 (p2_pin_spec t adds) Ht) in Hx. discriminate.
  - intros t Ht. apply in_app_or in Ht as [Ht|Ht].
    + left. unfold keep. rewrite (mv_negb_in (fst t) (map fst adds) (in_map fst _ _ Ht)), andb_false_r. reflexivity.
    + unfold X in Ht. apply filter_In in Ht as [_ Ht]. apply andb_true_iff in Ht as [_ Ht].
      apply negb_true_iff in Ht. apply andb_false_iff in Ht as [Ht|Ht]; [left; exact Ht|right].
      intros Hb. rewrite (proj2 (p2_pin_spec t (blocks L A)) Hb) in Ht. discriminate.
  - exact P1.
  - intros [q m] Ht. exact (P0 q m (ID _ Ht)).
  - exact Gn.
Qed.

Lemma p2_pos : forall (rc : RunCeil) B (API : AllocAPI B) L A mem md q m, aa_MR API L A mem md ->
  In (q, m) (blocks L A) -> 0 <= m.
Proof.
  intros rc B API L A mem md q m HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & Eq & Hp).
  injection Eq as <- <-. exact (AllocBound.ub_nonneg A (mr_wf _ _ (aa_laws API) _ _ _ _ HM) (p, n) Hp).
Qed.

Lemma p2_low : forall (rc : RunCeil) B (API : AllocAPI B) L A mem md q m, aa_MR API L A mem md ->
  In (q, m) (blocks L A) -> 4096 <= q.
Proof.
  intros rc B API L A mem md q m HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & Eq & Hp).
  injection Eq as <- <-. exact (proj1 (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ HM Hp)).
Qed.

Lemma p2_enc_eb : forall l x, In x (concat (map entry_nc l)) -> In x (concat (map entry_blocks l)).
Proof.
  intros l x H. apply in_concat in H as (y & Hy & Hx). apply in_map_iff in Hy as (e & <- & He).
  apply in_concat. exists (entry_blocks e). split; [apply in_map; exact He|].
  unfold entry_blocks. unfold entry_nc in Hx. rewrite app_assoc. apply in_or_app. left. exact Hx.
Qed.

Lemma p2_snc_hb : forall (l : list (hsrc * nat)) x, In x (concat (map (fun p => src_nc (fst p)) l)) ->
  In x (concat (map (fun p => hs_blocks (fst p)) l)).
Proof.
  intros l x H. apply in_concat in H as (y & Hy & Hx). apply in_map_iff in Hy as (p & <- & Hp).
  apply in_concat. exists (hs_blocks (fst p)). split; [exact (in_map (fun p => hs_blocks (fst p)) l p Hp)|].
  revert Hx. unfold src_nc, hs_blocks, list_blocks, arr_nc. rewrite !in_app_iff. tauto.
Qed.

Lemma p2_ta_perm : forall G O es hj,
  Permutation (target_addrs G O es hj) (rv_nc (view_of G O es hj) ++ p2_rest es hj).
Proof.
  intros G O es hj. apply p2_perm. intros x.
  assert (CE : forall l, count_occ Z.eq_dec (concat (map entry_blocks l)) x =
      (count_occ Z.eq_dec (concat (map entry_nc l)) x +
       count_occ Z.eq_dec (concat (map (fun e => map key_addr (re_keys e)) l)) x)%nat).
  { induction l as [|e l IH]; [reflexivity|]. cbn [map concat]. rewrite !count_occ_app, IH.
    unfold entry_blocks, entry_nc. rewrite !count_occ_app. lia. }
  assert (CH : forall l : list (hsrc * nat), count_occ Z.eq_dec (concat (map (fun p => hs_blocks (fst p)) l)) x =
      (count_occ Z.eq_dec (concat (map (fun p => src_nc (fst p)) l)) x +
       count_occ Z.eq_dec (concat (map (fun p => p2_srecs (fst p)) l)) x)%nat).
  { induction l as [|p l IH]; [reflexivity|]. cbn [map concat]. rewrite !count_occ_app, IH.
    unfold hs_blocks, list_blocks, src_nc, arr_nc, p2_srecs. rewrite !count_occ_app, !p2_cnt_cons, !p2_cnt_nil. lia. }
  unfold target_addrs, view_of, p2_rest. cbn [rv_nc]. p2_cr. rewrite CE, CH. lia.
Qed.

Lemma p2_ta_nd : forall G O es hj, List.NoDup (target_addrs G O es hj) ->
  List.NoDup (rv_nc (view_of G O es hj)) /\ (forall x, In x (rv_nc (view_of G O es hj)) -> ~ In x (p2_rest es hj)).
Proof.
  intros G O es hj H. pose proof (Permutation_NoDup (p2_ta_perm G O es hj) H) as H'.
  split; [exact (NoDup_app_remove_r _ _ H')|exact (p2_nd_disj _ _ H')].
Qed.

Lemma p2_rest_in : forall es hj h j x, In (h, j) hj -> In x (p2_srecs h) -> In x (p2_rest es hj).
Proof.
  intros es hj h j x Hh Hx. unfold p2_rest. apply in_or_app. right. apply in_concat. exists (p2_srecs h).
  split; [exact (in_map (fun p => p2_srecs (fst p)) hj (h, j) Hh)|exact Hx].
Qed.

Lemma p2_uniq : forall (L : layout) (A : astate) q m m', List.NoDup (map fst (blocks L A)) ->
  In (q, m) (blocks L A) -> In (q, m') (blocks L A) -> m = m'.
Proof. intros L A q m m' ND H1 H2. exact (mv_fst_uniq (blocks L A) q m m' ND H1 H2). Qed.

Lemma p2_arr_keep : forall (L : layout) (A : astate) (L' : layout) (A' : astate) (l l' : hlist) x m,
  List.NoDup (map fst (blocks L A)) ->
  (hl_cap l = 0 \/ In (hl_v l, 16 * hl_cap l) (blocks L A)) ->
  (hl_cap l' = 0 \/ In (hl_v l', 16 * hl_cap l') (blocks L' A')) ->
  hl_v l' = hl_v l -> hl_cap l' = hl_cap l -> In x (arr_nc l) -> In (x, m) (blocks L A) -> In (x, m) (blocks L' A').
Proof.
  intros L A L' A' l l' x m ND B0 B1 E1 E2 Hx Hm. unfold arr_nc in Hx.
  destruct (Z.eqb_spec (hl_cap l) 0) as [C|C]; [destruct Hx|]. destruct Hx as [<-|[]].
  destruct B0 as [B0|B0]; [contradiction|]. rewrite (p2_uniq L A _ _ _ ND Hm B0).
  destruct B1 as [B1|B1]; [rewrite E2 in B1; contradiction|]. rewrite E1, E2 in B1. exact B1.
Qed.

Lemma p2_drain_mv : forall (L : layout) (A : astate) (L' : layout) (A' : astate) (G O CAP q1 CAP' : Z)
    (es es' : list rentry) (hj hj' : list (hsrc * nat)) (pre post : list rentry) (hpre hpost : list (hsrc * nat))
    (e e' : rentry) (h h' : hsrc) (j : nat),
  es = pre ++ e :: post -> hj = hpre ++ (h, j) :: hpost -> es' = pre ++ e' :: post -> hj' = hpre ++ (h', j) :: hpost ->
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  List.NoDup (rv_nc (view_of G O es hj)) -> List.NoDup (rv_nc (view_of G q1 es' hj')) ->
  hl_v (hs_pending h') = hl_v (hs_pending h) -> hl_cap (hs_pending h') = hl_cap (hs_pending h) ->
  hs_partial h' = hs_partial h -> hs_held h' = hs_held h ->
  (forall x m, In (x, m) (blocks L A) ->
     In x (G :: concat (map entry_blocks pre) ++ concat (map entry_blocks post) ++
           concat (map (fun p => hs_blocks (fst p)) hpre) ++ concat (map (fun p => hs_blocks (fst p)) hpost)) ->
     In (x, m) (blocks L' A')) ->
  (hl_cap (hs_pending h) = 0 \/ In (hl_v (hs_pending h), 16 * hl_cap (hs_pending h)) (blocks L A)) ->
  (hl_cap (hs_pending h') = 0 \/ In (hl_v (hs_pending h'), 16 * hl_cap (hs_pending h')) (blocks L' A')) ->
  In (hs_partial h, 6000) (blocks L A) -> In (hs_partial h', 6000) (blocks L' A') ->
  (hl_cap (hs_held h) = 0 \/ In (hl_v (hs_held h), 16 * hl_cap (hs_held h)) (blocks L A)) ->
  (hl_cap (hs_held h') = 0 \/ In (hl_v (hs_held h'), 16 * hl_cap (hs_held h')) (blocks L' A')) ->
  (hl_cap (hs_expected h) = 0 \/ In (hl_v (hs_expected h), 16 * hl_cap (hs_expected h)) (blocks L A)) ->
  (hl_cap (hs_expected h') = 0 \/ In (hl_v (hs_expected h'), 16 * hl_cap (hs_expected h')) (blocks L' A')) ->
  (out_same O CAP q1 CAP' = true -> forall m, In (O, m) (blocks L A) -> In (O, m) (blocks L' A')) ->
  incl (out_move_dels O CAP q1 CAP') (blocks L A) -> incl (out_move_adds O CAP q1 CAP') (blocks L' A') ->
  (CAP = 0 -> forall m, ~ In (O, m) (blocks L A)) ->
  (re_cap e <> 0 -> In (re_buf e, re_cap e) (blocks L A)) -> (re_hp e <> 0 -> In (re_hp e, re_kh e) (blocks L A)) ->
  (re_cap e' <> 0 -> In (re_buf e', re_cap e') (blocks L' A')) ->
  (re_hp e' <> 0 -> In (re_hp e', re_kh e') (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 <= m) -> (forall q m, In (q, m) (blocks L' A') -> 0 <= m) ->
  nc_move (view_of G O es hj) L A (view_of G q1 es' hj') L' A'
    (p2_dr_dels O CAP q1 CAP' e e' (hs_expected h) (hs_expected h'))
    (p2_dr_adds O CAP q1 CAP' e e' (hs_expected h) (hs_expected h')).
Proof.
  intros L A L' A' G O CAP q1 CAP' es es' hj hj' pre post hpre hpost e e' h h' j -> -> -> -> ND0 ND1 NV NV'
    HP1 HP2 HPA HHL KO SB0 SB1 PT0 PT1 HL0 HL1 XB0 XB1 OS OD OA OG EB0 EH0 EB1 EH1 P0 P1.
  apply (p2_mv _ _ L A L' A' _ _
    ([G] ++ p2_oR O CAP q1 CAP' ++ concat (map entry_nc pre) ++ concat (map entry_nc post) ++
     concat (map (fun p => src_nc (fst p)) hpre) ++ concat (map (fun p => src_nc (fst p)) hpost) ++
     p2_bR e e' ++ p2_hR e e' ++ arr_nc (hs_pending h) ++ [hs_partial h] ++ arr_nc (hs_held h) ++
     p2_xR (hs_expected h) (hs_expected h'))
    (p2_gone O CAP q1 CAP') ND0 ND1 NV NV').
  - apply p2_perm. intros x. unfold view_of, p2_dr_dels. cbn [rv_nc]. rewrite !map_app, !concat_app.
    cbn [map concat fst]. rewrite (p2_enc e), (p2_snc h).
    pose proof (p2_cnt _ _ (p2_out_pd O CAP q1 CAP') x) as C1.
    pose proof (p2_cnt _ _ (p2_buf_pd e e') x) as C2.
    pose proof (p2_cnt _ _ (p2_hp_pd e e') x) as C3.
    pose proof (p2_cnt _ _ (p2_arr_pd (hs_expected h) (hs_expected h')) x) as C4.
    p2_cr. p2_crh C1. p2_crh C2. p2_crh C3. p2_crh C4. lia.
  - apply p2_perm. intros x. unfold view_of, p2_dr_adds. cbn [rv_nc]. rewrite !map_app, !concat_app.
    cbn [map concat fst]. rewrite (p2_enc e'), (p2_snc h').
    assert (EP : arr_nc (hs_pending h') = arr_nc (hs_pending h)) by (unfold arr_nc; rewrite HP1, HP2; reflexivity).
    rewrite EP, HPA, HHL.
    pose proof (p2_cnt _ _ (p2_out_pa O CAP q1 CAP') x) as C1.
    pose proof (p2_cnt _ _ (p2_buf_pa e e') x) as C2.
    pose proof (p2_cnt _ _ (p2_hp_pa e e') x) as C3.
    pose proof (p2_cnt _ _ (p2_arr_pa (hs_expected h) (hs_expected h')) x) as C4.
    p2_cr. p2_crh C1. p2_crh C2. p2_crh C3. p2_crh C4. lia.
  - intros t Ht. unfold p2_dr_dels in Ht. rewrite !in_app_iff in Ht. destruct Ht as [Ht|[Ht|[Ht|Ht]]].
    + exact (OD t Ht).
    + unfold p2_buf_dels in Ht. destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e') || (re_cap e =? 0)) eqn:C;
        [destruct Ht|]. destruct Ht as [<-|[]]. apply orb_false_iff in C as [_ C]. apply Z.eqb_neq in C. exact (EB0 C).
    + unfold p2_hp_dels in Ht. destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e') || (re_hp e =? 0)) eqn:C;
        [destruct Ht|]. destruct Ht as [<-|[]]. apply orb_false_iff in C as [_ C]. apply Z.eqb_neq in C. exact (EH0 C).
    + unfold p2_arr_dels in Ht. destruct (p2_same _ _ _ _); [destruct Ht|]. unfold arr_sz in Ht.
      destruct (Z.eqb_spec (hl_cap (hs_expected h)) 0) as [C|C]; [destruct Ht|]. destruct Ht as [<-|[]].
      destruct XB0 as [X|X]; [contradiction|exact X].
  - intros t Ht. unfold p2_dr_adds in Ht. rewrite !in_app_iff in Ht. destruct Ht as [Ht|[Ht|[Ht|Ht]]].
    + exact (OA t Ht).
    + unfold p2_buf_adds in Ht. destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e') || (re_cap e' =? 0)) eqn:C;
        [destruct Ht|]. destruct Ht as [<-|[]]. apply orb_false_iff in C as [_ C]. apply Z.eqb_neq in C. exact (EB1 C).
    + unfold p2_hp_adds in Ht. destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e') || (re_hp e' =? 0)) eqn:C;
        [destruct Ht|]. destruct Ht as [<-|[]]. apply orb_false_iff in C as [_ C]. apply Z.eqb_neq in C. exact (EH1 C).
    + unfold p2_arr_adds in Ht. destruct (p2_same _ _ _ _); [destruct Ht|]. unfold arr_sz in Ht.
      destruct (Z.eqb_spec (hl_cap (hs_expected h')) 0) as [C|C]; [destruct Ht|]. destruct Ht as [<-|[]].
      destruct XB1 as [X|X]; [contradiction|exact X].
  - intros x m Hx HR. rewrite !in_app_iff in HR.
    destruct HR as [HR|[HR|[HR|[HR|[HR|[HR|[HR|[HR|[HR|[HR|[HR|HR]]]]]]]]]]].
    + destruct HR as [<-|[]]. apply KO; [exact Hx|left; reflexivity].
    + unfold p2_oR in HR. destruct (out_same O CAP q1 CAP') eqn:S; [|destruct HR]. destruct HR as [<-|[]].
      exact (OS eq_refl m Hx).
    + apply KO; [exact Hx|right]. apply in_or_app. left. exact (p2_enc_eb _ _ HR).
    + apply KO; [exact Hx|right]. apply in_or_app. right. apply in_or_app. left. exact (p2_enc_eb _ _ HR).
    + apply KO; [exact Hx|right]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      exact (p2_snc_hb _ _ HR).
    + apply KO; [exact Hx|right]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      exact (p2_snc_hb _ _ HR).
    + unfold p2_bR in HR. destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e')) eqn:S; [|destruct HR].
      apply p2_same_eq in S as [S1 S2]. unfold p2_bnc in HR.
      destruct (Z.eqb_spec (re_cap e) 0) as [C|C]; [destruct HR|]. destruct HR as [<-|[]].
      rewrite (p2_uniq L A _ _ _ ND0 Hx (EB0 C)). rewrite <- S1, <- S2. apply EB1. rewrite S2. exact C.
    + unfold p2_hR in HR. destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e')) eqn:S; [|destruct HR].
      apply p2_same_eq in S as [S1 S2]. unfold p2_hnc in HR.
      destruct (Z.eqb_spec (re_hp e) 0) as [C|C]; [destruct HR|]. destruct HR as [<-|[]].
      rewrite (p2_uniq L A _ _ _ ND0 Hx (EH0 C)). rewrite <- S1, <- S2. apply EH1. rewrite S1. exact C.
    + exact (p2_arr_keep L A L' A' (hs_pending h) (hs_pending h') x m ND0 SB0 SB1 HP1 HP2 HR Hx).
    + destruct HR as [<-|[]]. rewrite (p2_uniq L A _ _ _ ND0 Hx PT0). rewrite <- HPA. exact PT1.
    + rewrite HHL in HL1. exact (p2_arr_keep L A L' A' (hs_held h) (hs_held h) x m ND0 HL0 HL1 eq_refl eq_refl HR Hx).
    + unfold p2_xR in HR. destruct (p2_same _ _ _ _) eqn:S; [|destruct HR]. apply p2_same_eq in S as [S1 S2].
      exact (p2_arr_keep L A L' A' (hs_expected h) (hs_expected h') x m ND0 XB0 XB1 S1 S2 HR Hx).
  - exact P0.
  - exact P1.
  - intros g Hg m. unfold p2_gone in Hg. destruct (out_same O CAP q1 CAP'); [destruct Hg|].
    destruct (Z.eqb_spec CAP 0) as [C|C]; [|destruct Hg]. destruct Hg as [<-|[]]. exact (OG C m).
Qed.

Lemma p2_cnl_mv : forall (L : layout) (A : astate) (L' : layout) (A' : astate) (G O : Z)
    (es es' : list rentry) (hj hj' : list (hsrc * nat)) (hpre hpost : list (hsrc * nat)) (h h' : hsrc) (j : nat),
  hj = hpre ++ (h, j) :: hpost -> hj' = hpre ++ (h', j) :: hpost ->
  concat (map entry_nc es') = concat (map entry_nc es) ->
  arr_nc (hs_pending h') = arr_nc (hs_pending h) -> hs_partial h' = hs_partial h ->
  arr_nc (hs_expected h') = arr_nc (hs_expected h) ->
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  List.NoDup (rv_nc (view_of G O es hj)) -> List.NoDup (rv_nc (view_of G O es' hj')) ->
  (forall x m, In (x, m) (blocks L A) -> In x (rv_nc (view_of G O es hj)) -> ~ In x (arr_nc (hs_held h)) ->
     In (x, m) (blocks L' A')) ->
  (hl_cap (hs_held h) = 0 \/ In (hl_v (hs_held h), 16 * hl_cap (hs_held h)) (blocks L A)) ->
  (hl_cap (hs_held h') = 0 \/ In (hl_v (hs_held h'), 16 * hl_cap (hs_held h')) (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 <= m) -> (forall q m, In (q, m) (blocks L' A') -> 0 <= m) ->
  nc_move (view_of G O es hj) L A (view_of G O es' hj') L' A'
    (p2_arr_dels (hs_held h) (hs_held h')) (p2_arr_adds (hs_held h) (hs_held h')).
Proof.
  intros L A L' A' G O es es' hj hj' hpre hpost h h' j -> -> EE EP EPA EX ND0 ND1 NV NV' KR HL0 HL1 P0 P1.
  set (Rr := G :: O :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hpre) ++
             concat (map (fun p => src_nc (fst p)) hpost) ++ arr_nc (hs_pending h) ++ [hs_partial h] ++
             arr_nc (hs_expected h)).
  assert (PR : Permutation (rv_nc (view_of G O es (hpre ++ (h, j) :: hpost))) (Rr ++ arr_nc (hs_held h))).
  { apply p2_perm. intros x. unfold view_of, Rr. cbn [rv_nc]. rewrite !map_app, !concat_app. cbn [map concat fst].
    rewrite (p2_snc h). p2_cr. lia. }
  pose proof (Permutation_NoDup PR NV) as NR.
  apply (p2_mv _ _ L A L' A' _ _ (Rr ++ p2_xR (hs_held h) (hs_held h')) [] ND0 ND1 NV NV').
  - apply p2_perm. intros x. rewrite (p2_cnt _ _ PR x).
    pose proof (p2_cnt _ _ (p2_arr_pd (hs_held h) (hs_held h')) x) as C1.
    p2_cr. p2_crh C1. lia.
  - apply p2_perm. intros x. unfold view_of, Rr. cbn [rv_nc]. rewrite EE, !map_app, !concat_app. cbn [map concat fst].
    rewrite (p2_snc h'), EP, EPA, EX.
    pose proof (p2_cnt _ _ (p2_arr_pa (hs_held h) (hs_held h')) x) as C1.
    p2_cr. p2_crh C1. lia.
  - intros t Ht. unfold p2_arr_dels in Ht. destruct (p2_same _ _ _ _); [destruct Ht|]. unfold arr_sz in Ht.
    destruct (Z.eqb_spec (hl_cap (hs_held h)) 0) as [C|C]; [destruct Ht|]. destruct Ht as [<-|[]].
    destruct HL0 as [X|X]; [contradiction|exact X].
  - intros t Ht. unfold p2_arr_adds in Ht. destruct (p2_same _ _ _ _); [destruct Ht|]. unfold arr_sz in Ht.
    destruct (Z.eqb_spec (hl_cap (hs_held h')) 0) as [C|C]; [destruct Ht|]. destruct Ht as [<-|[]].
    destruct HL1 as [X|X]; [contradiction|exact X].
  - intros x m Hx HR. apply in_app_or in HR as [HR|HR].
    + apply KR; [exact Hx| |exact (p2_nd_disj _ _ NR x HR)].
      apply (Permutation_in _ (Permutation_sym PR)). apply in_or_app. left. exact HR.
    + unfold p2_xR in HR. destruct (p2_same _ _ _ _) eqn:S; [|destruct HR]. apply p2_same_eq in S as [S1 S2].
      exact (p2_arr_keep L A L' A' (hs_held h) (hs_held h') x m ND0 HL0 HL1 S1 S2 HR Hx).
  - exact P0.
  - exact P1.
  - intros g [].
Qed.

Definition drain_wt (es : list rentry) (hj : list (hsrc * nat)) (e : rentry) (h : hsrc) (fin : dstate) : Z :=
  nc_wt es hj - nw_ent e - nw_src h +
  (Z.max (ds_cap fin) (DATA_PER * Z.of_nat (length (ds_u fin)) + 8192) +
   Z.max (ds_ka fin) (8 * Z.of_nat (length (ds_H fin)) + 8)) +
  (Z.max (16 * hl_cap (hs_pending h)) 128 + PARTIAL_BYTES +
   Z.max (16 * ds_ecap fin)
     (NC_PER * (hl_n (hs_expected h) + Z.of_nat (length (lines (hs_state h) (bzs (pending_stream h))))) + 128) +
   nw_list (hs_held h)).

Definition cnl_wt (es : list rentry) (hj : list (hsrc * nat)) (h : hsrc) : Z :=
  nc_wt es hj + NC_PER * Z.of_nat (count_begin (texts (hs_expected h))).

Lemma p2_wt_repl : forall es1 e es2 hj1 h j hj2 e' h' j',
  nc_wt (es1 ++ e' :: es2) (hj1 ++ (h', j') :: hj2) =
  nc_wt (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2) - nw_ent e - nw_src h + nw_ent e' + nw_src h'.
Proof.
  intros es1 e es2 hj1 h j hj2 e' h' j'. unfold nc_wt.
  rewrite !AllocBound.zsum_app, !AllocBound.zsum_cons, !length_app. cbn [length fst]. cbv beta.
  unfold NW_ENT0, NW_SRC0. lia.
Qed.

Lemma drain_wt_post : forall es1 es2 hj1 hj2 e e' h h' j j' fin,
  re_cap e' = ds_cap fin -> Z.of_nat (length (re_U e')) = re_used e' -> bzs (re_U e') = ds_u fin ->
  ent_ka e' = ds_ka fin -> keys_texts (re_keys e') = ds_H fin ->
  hl_recs (hs_pending h') = [] -> hl_cap (hs_pending h') = hl_cap (hs_pending h) ->
  hl_cap (hs_expected h') = ds_ecap fin ->
  map snd (hl_recs (hs_expected h')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines (hs_state h) (bzs (pending_stream h))) ->
  hs_held h' = hs_held h ->
  nc_wt (es1 ++ e' :: es2) (hj1 ++ (h', j') :: hj2) = drain_wt (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2) e h fin.
Proof.
  intros es1 es2 hj1 hj2 e e' h h' j j' fin C1 U1 U2 K1 K2 P1 P2 X1 X2 H1.
  rewrite (p2_wt_repl es1 e es2 hj1 h j hj2 e' h' j').
  assert (LU : Z.of_nat (length (ds_u fin)) = re_used e') by (rewrite <- U2; unfold bzs; rewrite length_map; exact U1).
  assert (LK : Z.of_nat (length (ds_H fin)) = re_nheld e')
    by (rewrite <- K2; unfold keys_texts, re_nheld; rewrite length_map; reflexivity).
  assert (LX : hl_n (hs_expected h') =
      hl_n (hs_expected h) + Z.of_nat (length (lines (hs_state h) (bzs (pending_stream h))))).
  { unfold hl_n. rewrite <- (length_map snd (hl_recs (hs_expected h'))), X2, length_app, !length_map. lia. }
  assert (PS : pending_stream h' = []) by (unfold pending_stream; rewrite P1; reflexivity).
  assert (PN : hl_n (hs_pending h') = 0) by (unfold hl_n; rewrite P1; reflexivity).
  assert (W1 : nw_ent e' = Z.max (ds_cap fin) (DATA_PER * Z.of_nat (length (ds_u fin)) + 8192) +
      Z.max (ds_ka fin) (8 * Z.of_nat (length (ds_H fin)) + 8)).
  { rewrite LU, LK, <- C1, <- K1. reflexivity. }
  assert (W2 : nw_src h' = Z.max (16 * hl_cap (hs_pending h)) 128 + PARTIAL_BYTES +
      Z.max (16 * ds_ecap fin)
        (NC_PER * (hl_n (hs_expected h) + Z.of_nat (length (lines (hs_state h) (bzs (pending_stream h))))) + 128) +
      nw_list (hs_held h)).
  { unfold nw_src. rewrite PS, H1, <- X1, <- LX. unfold nw_list. rewrite PN, P2. cbn [length Z.of_nat].
    unfold DATA_PER, NC_PER. lia. }
  unfold drain_wt. rewrite W1, W2. lia.
Qed.

Lemma p2_filter_len : forall {X} (f : X -> bool) (l : list X), (length (filter f l) <= length l)%nat.
Proof. intros X f l. induction l as [|x l IH]; [reflexivity|]. cbn [filter length]. destruct (f x); cbn [length]; lia. Qed.

Lemma p2_cb_cons : forall l Ls, count_begin (l :: Ls) = (if is_begin l then S (count_begin Ls) else count_begin Ls).
Proof. intros l Ls. unfold count_begin. cbn. destruct (is_begin l); reflexivity. Qed.

Lemma p2_upds_len : forall Ls G, (length (upds G Ls) <= length G + count_begin Ls)%nat.
Proof.
  unfold upds. induction Ls as [|l Ls IH]; intros G; cbn [fold_left]; [unfold count_begin; cbn; lia|].
  rewrite p2_cb_cons. pose proof (IH (upd G l)) as X.
  assert (U : (length (upd G l) <= length G + (if is_begin l then 1 else 0))%nat).
  { unfold upd, is_begin. destruct (gesture l) as [[[|] x]|].
    - destruct (existsb (list_eqb x) G); [lia|rewrite length_app; cbn [length]; lia].
    - pose proof (p2_filter_len (fun y => negb (list_eqb x y)) G). lia.
    - lia. }
  destruct (is_begin l); cbv beta iota in U; lia.
Qed.

Lemma p2_wt_src : forall es hj1 h j hj2 h' j',
  nc_wt es (hj1 ++ (h', j') :: hj2) = nc_wt es (hj1 ++ (h, j) :: hj2) - nw_src h + nw_src h'.
Proof.
  intros es hj1 h j hj2 h' j'. unfold nc_wt. rewrite !AllocBound.zsum_app, !AllocBound.zsum_cons, !length_app.
  cbn [length fst]. cbv beta. unfold NW_ENT0, NW_SRC0. lia.
Qed.

Lemma cnl_wt_post : forall es hj1 hj2 h j E' H',
  hl_recs E' = [] -> hl_cap E' = hl_cap (hs_expected h) ->
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) ->
  texts H' = upds (texts (hs_held h)) (texts (hs_expected h)) ->
  nc_wt es (hj1 ++ (set_exp_held h E' H', j) :: hj2) <= cnl_wt es (hj1 ++ (h, j) :: hj2) h.
Proof.
  intros es hj1 hj2 h j E' H' ER EC HC HT. unfold cnl_wt.
  rewrite (p2_wt_src es hj1 h j hj2 (set_exp_held h E' H') j).
  assert (NH : (length (hl_recs H') <= length (hl_recs (hs_held h)) + count_begin (texts (hs_expected h)))%nat).
  { pose proof (p2_upds_len (texts (hs_expected h)) (texts (hs_held h))) as X. rewrite <- HT in X.
    assert (T1 : length (texts H') = length (hl_recs H')) by (unfold texts; apply length_map).
    assert (T2 : length (texts (hs_held h)) = length (hl_recs (hs_held h))) by (unfold texts; apply length_map).
    rewrite T1, T2 in X. exact X. }
  assert (NE : nw_list E' <= nw_list (hs_expected h)).
  { unfold nw_list, hl_n. rewrite ER, EC. cbn [length Z.of_nat]. unfold NC_PER. lia. }
  assert (NHW : nw_list H' <= nw_list (hs_held h) + NC_PER * Z.of_nat (count_begin (texts (hs_expected h)))).
  { unfold nw_list, hl_n in *. unfold NC_PER. lia. }
  assert (PS : pending_stream (set_exp_held h E' H') = pending_stream h) by reflexivity.
  unfold nw_src. rewrite PS. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held]. lia.
Qed.

Lemma p2_zsum_perm : forall {X} (f : X -> Z) (l l' : list X), Permutation l l' ->
  AllocBound.zsum f l = AllocBound.zsum f l'.
Proof.
  intros X f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2].
  - reflexivity.
  - rewrite !AllocBound.zsum_cons, IH. reflexivity.
  - rewrite !AllocBound.zsum_cons. lia.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma p4_wt_remove : forall es hj e p es' hj',
  Permutation es (e :: es') -> Permutation hj (p :: hj') -> 0 <= re_used e ->
  nc_wt es' hj' <= nc_wt es hj.
Proof.
  intros es hj e p es' hj' PE PH U. unfold nc_wt.
  rewrite (p2_zsum_perm nw_ent _ _ PE), (p2_zsum_perm (fun p => nw_src (fst p)) _ _ PH), !AllocBound.zsum_cons.
  rewrite (Permutation_length PE), (Permutation_length PH). cbn [length]. cbv beta.
  assert (W1 : NW_ENT0 <= nw_ent e) by (unfold nw_ent, NW_ENT0, DATA_PER, re_nheld; lia).
  assert (W2 : NW_SRC0 <= nw_src (fst p)) by (unfold nw_src, nw_list, NW_SRC0, NC_PER, DATA_PER, PARTIAL_BYTES, hl_n; lia).
  unfold NW_ENT0, NW_SRC0 in *. lia.
Qed.

Definition p2_lb (L : layout) (A : astate) (l : hlist) : Prop := hl_cap l = 0 \/ In (hl_v l, 16 * hl_cap l) (blocks L A).

Definition p2_eb (L : layout) (A : astate) (e : rentry) : Prop :=
  (re_cap e = 0 \/ In (re_buf e, re_cap e) (blocks L A)) /\ (re_hp e = 0 \/ In (re_hp e, re_kh e) (blocks L A)).

Definition p2_sb (L : layout) (A : astate) (h : hsrc) : Prop :=
  p2_lb L A (hs_pending h) /\ In (hs_partial h, 6000) (blocks L A) /\ p2_lb L A (hs_expected h) /\
  p2_lb L A (hs_held h).

Lemma p2_lb_wt : forall L A l, List.NoDup (map fst (blocks L A)) -> p2_lb L A l ->
  AllocBound.zsum (SlotRI3.nc_sz L A) (arr_nc l) <= nw_list l.
Proof.
  intros L A l HN H. unfold arr_nc, nw_list, NC_PER, hl_n.
  destruct (Z.eqb_spec (hl_cap l) 0) as [C|C]; [rewrite AllocBound.zsum_nil; lia|].
  destruct H as [H|Hin]; [contradiction|].
  rewrite AllocBound.zsum_cons, AllocBound.zsum_nil, (SlotNcWt.nw_sz_at L A _ _ HN Hin). lia.
Qed.

Lemma p2_eb_wt : forall L A e, List.NoDup (map fst (blocks L A)) -> p2_eb L A e ->
  AllocBound.zsum (SlotRI3.nc_sz L A) (entry_nc e) <= nw_ent e.
Proof.
  intros L A e HN (Hb & Hh). unfold entry_nc, nw_ent, DATA_PER. rewrite AllocBound.zsum_app.
  assert (X1 : AllocBound.zsum (SlotRI3.nc_sz L A) (if re_cap e =? 0 then [] else [re_buf e]) <= re_cap e).
  { destruct (Z.eqb_spec (re_cap e) 0) as [E0|E0]; [rewrite AllocBound.zsum_nil; lia|].
    destruct Hb as [Hb|Hb]; [contradiction|].
    rewrite AllocBound.zsum_cons, AllocBound.zsum_nil, (SlotNcWt.nw_sz_at L A _ _ HN Hb). lia. }
  assert (X2 : AllocBound.zsum (SlotRI3.nc_sz L A) (if re_hp e =? 0 then [] else [re_hp e]) <=
      (if re_hp e =? 0 then 0 else re_kh e)).
  { destruct (Z.eqb_spec (re_hp e) 0) as [E0|E0]; [rewrite AllocBound.zsum_nil; lia|].
    destruct Hh as [Hh|Hh]; [contradiction|].
    rewrite AllocBound.zsum_cons, AllocBound.zsum_nil, (SlotNcWt.nw_sz_at L A _ _ HN Hh). lia. }
  lia.
Qed.

Lemma p2_sb_wt : forall L A h, List.NoDup (map fst (blocks L A)) -> p2_sb L A h ->
  AllocBound.zsum (SlotRI3.nc_sz L A) (src_nc h) <= nw_src h.
Proof.
  intros L A h HN (Lp & Pp & Le & Lh). unfold src_nc, nw_src.
  rewrite !AllocBound.zsum_app, AllocBound.zsum_cons, AllocBound.zsum_nil, (SlotNcWt.nw_sz_at L A _ _ HN Pp).
  pose proof (p2_lb_wt L A _ HN Lp). pose proof (p2_lb_wt L A _ HN Le). pose proof (p2_lb_wt L A _ HN Lh).
  pose proof (Zle_0_nat (length (pending_stream h))). unfold DATA_PER, PARTIAL_BYTES. lia.
Qed.

Lemma p2_ncs_wt : forall L A G OUT es hj, List.NoDup (map fst (blocks L A)) ->
  SlotRI3.nc_sz L A G <= SRC_TABLE -> SlotRI3.nc_sz L A OUT <= TBBYTES ->
  Forall (p2_eb L A) es -> Forall (fun p => p2_sb L A (fst p)) hj ->
  (length es <= 4)%nat -> (length hj <= 4)%nat ->
  SlotRI3.ncs (view_of G OUT es hj) L A <= nc_wt es hj.
Proof.
  intros L A G OUT es hj HN HG HO HE HS Hes Hhj.
  assert (XE : AllocBound.zsum (SlotRI3.nc_sz L A) (concat (map entry_nc es)) <= AllocBound.zsum nw_ent es).
  { rewrite SlotNcWt.nw_zsum_concat. apply SlotNcWt.nw_zsum_le. intros e He.
    rewrite Forall_forall in HE. exact (p2_eb_wt L A e HN (HE e He)). }
  assert (XS : AllocBound.zsum (SlotRI3.nc_sz L A) (concat (map (fun p => src_nc (fst p)) hj)) <=
      AllocBound.zsum (fun p => nw_src (fst p)) hj).
  { rewrite SlotNcWt.nw_zsum_concat. apply SlotNcWt.nw_zsum_le. intros p Hp.
    rewrite Forall_forall in HS. exact (p2_sb_wt L A (fst p) HN (HS p Hp)). }
  unfold SlotRI3.ncs, view_of, nc_wt. cbn [rv_nc]. rewrite !AllocBound.zsum_cons, AllocBound.zsum_app.
  unfold NW_ENT0, NW_SRC0, PARTIAL_BYTES. lia.
Qed.

Lemma p2_eb_keep : forall L A L' A' e,
  (forall x m, In (x, m) (blocks L A) -> In x (entry_blocks e) -> In (x, m) (blocks L' A')) ->
  p2_eb L A e -> p2_eb L' A' e.
Proof.
  intros L A L' A' e K (Hb & Hh). unfold entry_blocks in K. split.
  - destruct Hb as [Hb|Hb]; [left; exact Hb|]. destruct (Z.eq_dec (re_cap e) 0) as [C|C]; [left; exact C|right].
    apply (K _ _ Hb). rewrite (proj2 (Z.eqb_neq _ _) C). apply in_or_app. left. left. reflexivity.
  - destruct Hh as [Hh|Hh]; [left; exact Hh|]. destruct (Z.eq_dec (re_hp e) 0) as [C|C]; [left; exact C|right].
    apply (K _ _ Hh). apply in_or_app. right. rewrite (proj2 (Z.eqb_neq _ _) C). apply in_or_app. left. left.
    reflexivity.
Qed.

Lemma p2_lb_keep : forall L A L' A' l (S : list Z),
  (forall x m, In (x, m) (blocks L A) -> In x S -> In (x, m) (blocks L' A')) ->
  (forall x, In x (list_blocks l) -> In x S) -> p2_lb L A l -> p2_lb L' A' l.
Proof.
  intros L A L' A' l S K I [C|Hin]; [left; exact C|].
  destruct (Z.eq_dec (hl_cap l) 0) as [C|C]; [left; exact C|right].
  apply (K _ _ Hin). apply I. unfold list_blocks. rewrite (proj2 (Z.eqb_neq _ _) C). apply in_or_app. left. left.
  reflexivity.
Qed.

Lemma p2_sb_keep : forall L A L' A' h,
  (forall x m, In (x, m) (blocks L A) -> In x (hs_blocks h) -> In (x, m) (blocks L' A')) ->
  p2_sb L A h -> p2_sb L' A' h.
Proof.
  intros L A L' A' h K (Lp & Pp & Le & Lh). split; [|split; [|split]].
  - apply (p2_lb_keep L A L' A' _ _ K); [|exact Lp]. intros x Hx. unfold hs_blocks. apply in_or_app. left. exact Hx.
  - apply (K _ _ Pp). unfold hs_blocks. apply in_or_app. right. left. reflexivity.
  - apply (p2_lb_keep L A L' A' _ _ K); [|exact Le]. intros x Hx. unfold hs_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hx.
  - apply (p2_lb_keep L A L' A' _ _ K); [|exact Lh]. intros x Hx. unfold hs_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hx.
Qed.

Lemma p2_nc_keep : forall V L A V' L' A' dels adds,
  WF A -> layout_le A L L' -> nc_move V L A V' L' A' dels adds ->
  forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') -> In (ptr_addr L p) (rv_nc V) ->
    ~ In (ptr_addr L p) (map fst dels) -> In (ptr_addr L' p) (rv_nc V').
Proof.
  intros V L A V' L' A' dels adds HW HL (R & gone & Bk & X & Y & HV & HV' & _ & _ & _ & _ & _ & _ & _ & HG)
    p n n' Hp _ Hin Hnd.
  rewrite (ListFrame.lf_addr A L L' p n HW HL Hp).
  apply (Permutation_in _ HV) in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply (Permutation_in _ (Permutation_sym HV')). apply in_or_app. left. exact Hin.
  - apply in_app_or in Hin as [Hin|Hin]; [contradiction|].
    exfalso. apply (HG _ Hin n). unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hp).
Qed.
