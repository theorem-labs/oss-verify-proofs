From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF HarnessRep RelayRep ListRep ListTr HarnessTr CheckRep relay_add_b_c
  op_add_c send_line_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_finish_b_c SlotMove SlotNcMove3 SlotRun3
  SlotOp7R3 SlotResR3 SlotResReply SlotExitFinRes.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mv_inb (x : Z) l : existsb (Z.eqb x) l = true <-> In x l.
Proof.
  rewrite existsb_exists. split.
  - intros (y & Hy & E). apply Z.eqb_eq in E. subst y. exact Hy.
  - intros Hx. exists x. split; [exact Hx|apply Z.eqb_refl].
Qed.

Lemma mv_app {X : Type} (l1 l2 : list X) : List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
  List.NoDup (l1 ++ l2).
Proof.
  intros H1 H2 H3. induction H1 as [|x l Hx Hl IH]; [exact H2|]. cbn [app]. constructor.
  - intros Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (Hx Hin)|exact (H3 x (or_introl eq_refl) Hin)].
  - apply IH. intros a Ha. apply H3. right. exact Ha.
Qed.

Lemma mv_disj {X : Type} (l1 l2 : list X) x : List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros H H1 H2; [destruct H1|].
  cbn [app] in H. apply NoDup_cons_iff in H as [Hy H].
  destruct H1 as [<-|H1]; [apply Hy; apply in_or_app; right; exact H2|exact (IH H H1 H2)].
Qed.

Lemma mv_fst_eq (l : list (Z * Z)) t u : List.NoDup (map fst l) -> In t l -> In u l -> fst t = fst u -> t = u.
Proof.
  induction l as [|v l IH]; intros HN Ht Hu He; [destruct Ht|].
  cbn [map] in HN. apply NoDup_cons_iff in HN as [Hv HN].
  destruct Ht as [<-|Ht]; destruct Hu as [<-|Hu].
  - reflexivity.
  - exfalso. apply Hv. rewrite He. apply in_map. exact Hu.
  - exfalso. apply Hv. rewrite <- He. apply in_map. exact Ht.
  - exact (IH HN Ht Hu He).
Qed.

Lemma mv_nd_mapfilter (f : Z * Z -> bool) (l : list (Z * Z)) : List.NoDup (map fst l) ->
  List.NoDup (map fst (filter f l)).
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [map] in H. apply NoDup_cons_iff in H as [Hx H].
  cbn [filter]. destruct (f x); [|exact (IH H)]. cbn [map]. constructor; [|exact (IH H)].
  intros Hin. apply Hx. apply in_map_iff in Hin as (y & Ey & Hy). apply filter_In in Hy as [Hy _].
  rewrite <- Ey. apply in_map. exact Hy.
Qed.

Lemma mv_filter_len {X : Type} (f : X -> bool) l : (length (filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; [cbn; lia|]. cbn [filter length]. destruct (f x); cbn [length]; lia. Qed.

Definition mv_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Definition mv_keep (D : list (Z * Z)) (t : Z * Z) : bool := if in_dec mv_dec t D then false else true.

Lemma mv_keep_spec D t : mv_keep D t = true <-> ~ In t D.
Proof.
  unfold mv_keep. destruct (in_dec mv_dec t D) as [X|X]; split; intros H.
  - discriminate H.
  - contradiction.
  - exact X.
  - reflexivity.
Qed.

Lemma nc_move_mk V L A V' L' A' dels adds R gone Y :
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  Permutation (rv_nc V) (R ++ map fst dels ++ gone) -> Permutation (rv_nc V') (R ++ map fst adds) ->
  List.NoDup (map fst (dels ++ Y)) -> List.NoDup adds -> incl (dels ++ Y) (blocks L A) ->
  (forall t, In t (blocks L' A') <-> (In t (blocks L A) /\ ~ In t (dels ++ Y)) \/ In t adds) ->
  (forall t, In t adds -> In t (blocks L A) -> In t (dels ++ Y)) ->
  (forall q m, In (q, m) (blocks L' A') -> 0 <= m) ->
  (forall t, In t dels -> 0 <= snd t) -> (forall t, In t (dels ++ Y) -> ~ In (fst t) R) ->
  (forall g, In g gone -> forall m, ~ In (g, m) (blocks L A)) ->
  nc_move V L A V' L' A' dels adds.
Proof.
  intros NK NP HV HV' ND NA HI HP HA Hpos Hdel HR Hg.
  pose proof (NoDup_map_inv _ _ NK) as NK'. pose proof (NoDup_map_inv _ _ NP) as NP'.
  pose proof (NoDup_map_inv _ _ ND) as ND'.
  remember (filter (mv_keep (dels ++ Y)) (blocks L A)) as Bl eqn:HBl.
  assert (InB : forall t, In t Bl <-> In t (blocks L A) /\ ~ In t (dels ++ Y)).
  { intros t. rewrite HBl, filter_In, mv_keep_spec. tauto. }
  assert (NB : List.NoDup Bl) by (rewrite HBl; apply NoDup_filter; exact NK').
  exists R, gone, Bl, [], Y.
  split; [exact HV|]. split; [exact HV'|].
  split.
  { apply NoDup_Permutation; [exact NK'| |].
    - apply mv_app; [exact NB|exact ND'|]. intros t Ht. exact (proj2 (proj1 (InB t) Ht)).
    - intros t. rewrite in_app_iff, InB. split.
      + intros Ht. destruct (in_dec mv_dec t (dels ++ Y)) as [X|X]; [right; exact X|left; split; assumption].
      + intros [[X _]|X]; [exact X|exact (HI t X)]. }
  split.
  { rewrite app_nil_r. apply NoDup_Permutation; [exact NP'| |].
    - apply mv_app; [exact NB|exact NA|]. intros t Ht Ha. apply (proj2 (proj1 (InB t) Ht)).
      exact (HA t Ha (proj1 (proj1 (InB t) Ht))).
    - intros t. rewrite in_app_iff, InB. exact (HP t). }
  split; [exact Hpos|]. split; [exact Hdel|].
  split; [rewrite map_app in ND; exact (NoDup_app_remove_r _ _ ND)|].
  split.
  { intros t Ht. split; [apply HR; apply in_or_app; left; exact Ht|].
    intros m Hm. apply InB in Hm as (Hm & Nm). apply Nm.
    assert (Ht' : In t (blocks L A)) by (apply HI; apply in_or_app; left; exact Ht).
    rewrite (mv_fst_eq (blocks L A) (fst t, m) t NK Hm Ht' eq_refl). apply in_or_app. left. exact Ht. }
  split.
  { intros t Ht. split; [apply HR; apply in_or_app; right; exact Ht|].
    intros X. rewrite map_app in ND. apply (mv_disj _ _ (fst t) ND X). apply in_map. exact Ht. }
  exact Hg.
Qed.

Lemma mv_same V L A L' A' : (forall q m, In (q, m) (blocks L A) -> 0 <= m) -> blocks L' A' = blocks L A ->
  nc_move V L A V L' A' [] [].
Proof.
  intros KB EQ. exists (rv_nc V), [], (blocks L A), [], [].
  split; [cbn [map app]; rewrite app_nil_r; apply Permutation_refl|].
  split; [cbn [map]; rewrite app_nil_r; apply Permutation_refl|].
  split; [cbn [app]; rewrite app_nil_r; apply Permutation_refl|].
  split; [rewrite EQ; cbn [app]; rewrite app_nil_r; apply Permutation_refl|].
  split; [intros q m H; rewrite EQ in H; exact (KB q m H)|].
  split; [intros t []|]. split; [cbn [map]; constructor|].
  split; [intros t []|]. split; [intros t []|]. intros g [].
Qed.

Lemma mv_snc_hb h q : In q (src_nc h) -> In q (hs_blocks h).
Proof. unfold src_nc, hs_blocks, list_blocks, arr_nc. rewrite !in_app_iff. tauto. Qed.

Lemma mv_sr_hb (hj : list (hsrc * nat)) q : In q (concat (map (fun p => src_nc (fst p)) hj)) ->
  In q (concat (map (fun p => hs_blocks (fst p)) hj)).
Proof.
  intros H. apply in_concat in H as (l & Hl & Hq). apply in_map_iff in Hl as (p & <- & Hp).
  apply in_concat. exists (hs_blocks (fst p)). split; [apply in_map_iff; exists p; split; [reflexivity|exact Hp]|].
  exact (mv_snc_hb _ _ Hq).
Qed.

Lemma mv_hb_perm h : Permutation (hs_blocks h)
  (src_nc h ++ map fst (hl_recs (hs_pending h)) ++ map fst (hl_recs (hs_expected h)) ++ map fst (hl_recs (hs_held h))).
Proof.
  apply (Permutation_count_occ Z.eq_dec). intros x.
  unfold hs_blocks, list_blocks, src_nc, arr_nc. rewrite !count_occ_app. lia.
Qed.

Lemma mv_snc_nd h : List.NoDup (hs_blocks h) -> List.NoDup (src_nc h).
Proof. intros H. exact (NoDup_app_remove_r _ _ (Permutation_NoDup (mv_hb_perm h) H)). Qed.

Lemma mv_rec_nc h : List.NoDup (hs_blocks h) -> forall q, In q (map fst (hl_recs (hs_held h))) -> ~ In q (src_nc h).
Proof.
  intros H q Hq Hs. apply (mv_disj _ _ q (Permutation_NoDup (mv_hb_perm h) H) Hs).
  rewrite !in_app_iff. right. right. exact Hq.
Qed.

Lemma mv_src_fst h : map fst (src_dels h) = src_nc h.
Proof.
  unfold src_dels, src_nc, arr_sz, arr_nc.
  destruct (hl_cap (hs_pending h) =? 0); destruct (hl_cap (hs_expected h) =? 0); destruct (hl_cap (hs_held h) =? 0);
    reflexivity.
Qed.

Lemma mv_set_held_nc h l : hl_v l = hl_v (hs_held h) -> hl_cap l = hl_cap (hs_held h) ->
  src_nc (set_held h l) = src_nc h.
Proof. intros E1 E2. unfold src_nc, arr_nc, set_held. cbn [hs_pending hs_partial hs_expected hs_held]. rewrite E1, E2. reflexivity. Qed.

Lemma mv_ent_fst es : map fst (ent_dels es) = concat (map entry_nc es).
Proof.
  unfold ent_dels. induction es as [|e es IH]; [reflexivity|]. cbn [map concat]. rewrite !map_app, IH.
  unfold entry_nc. destruct (re_cap e =? 0); destruct (re_hp e =? 0); reflexivity.
Qed.

Definition mv_ka (es : list rentry) : list Z := concat (map (fun e => map key_addr (re_keys e)) es).

Lemma mv_eb e : entry_blocks e = entry_nc e ++ map key_addr (re_keys e).
Proof. unfold entry_blocks, entry_nc. rewrite app_assoc. reflexivity. Qed.

Lemma mv_eb_perm es : Permutation (concat (map entry_blocks es)) (concat (map entry_nc es) ++ mv_ka es).
Proof.
  unfold mv_ka. induction es as [|e es IH]; [cbn; constructor|]. cbn [map concat]. rewrite mv_eb.
  rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
  rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

Lemma mv_ent_blk L A es :
  Forall (fun e => (re_cap e <> 0 -> In (re_buf e, re_cap e) (blocks L A) /\ 0 <= re_cap e) /\
                   (re_hp e <> 0 -> In (re_hp e, re_kh e) (blocks L A) /\ 0 <= re_kh e)) es ->
  forall t, In t (ent_dels es) -> In t (blocks L A) /\ 0 <= snd t.
Proof.
  intros HE t Ht. unfold ent_dels in Ht. apply in_concat in Ht as (l & Hl & Ht).
  apply in_map_iff in Hl as (e & <- & He). rewrite Forall_forall in HE. destruct (HE e He) as (H1 & H2).
  apply in_app_iff in Ht as [Ht|Ht].
  - revert Ht. destruct (Z.eqb_spec (re_cap e) 0) as [C|C]; intros Ht; [destruct Ht|].
    destruct Ht as [<-|[]]. exact (H1 C).
  - revert Ht. destruct (Z.eqb_spec (re_hp e) 0) as [C|C]; intros Ht; [destruct Ht|].
    destruct Ht as [<-|[]]. exact (H2 C).
Qed.

Lemma mv_target G OUT es hj : List.NoDup (target_addrs G OUT es hj) ->
  G <> OUT /\ ~ In G (concat (map entry_blocks es)) /\ ~ In G (concat (map (fun p => hs_blocks (fst p)) hj)) /\
  ~ In OUT (concat (map entry_blocks es)) /\ ~ In OUT (concat (map (fun p => hs_blocks (fst p)) hj)) /\
  List.NoDup (concat (map entry_blocks es)) /\
  (forall q, In q (concat (map entry_blocks es)) -> ~ In q (concat (map (fun p => hs_blocks (fst p)) hj))).
Proof.
  unfold target_addrs. intros H. apply NoDup_cons_iff in H as [H1 H]. apply NoDup_cons_iff in H as [H2 H].
  split; [intros E; apply H1; left; exact (eq_sym E)|].
  split; [intros X; apply H1; right; apply in_or_app; left; exact X|].
  split; [intros X; apply H1; right; apply in_or_app; right; exact X|].
  split; [intros X; apply H2; apply in_or_app; left; exact X|].
  split; [intros X; apply H2; apply in_or_app; right; exact X|].
  split; [exact (NoDup_app_remove_r _ _ H)|].
  intros q X Y. exact (mv_disj _ _ q H X Y).
Qed.

Lemma mv_fin_cap_off mx : forall es no cap, relay_finish_cap false mx no cap es = cap.
Proof. intros es no cap. apply fin_cap_off. Qed.

Section Blk.
Context {rc : RunCeil}.

Lemma mv_blk B (API : AllocAPI B) L A mem md q m : aa_MR API L A mem md -> In (q, m) (blocks L A) ->
  0 <= m /\ 4096 <= q.
Proof.
  intros HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & Eq & Hp). injection Eq as <- <-.
  split.
  - exact (ub_nonneg A (mr_wf _ _ (aa_laws API) _ _ _ _ HM) (p, n) Hp).
  - exact (proj1 (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ HM Hp)).
Qed.

Lemma mv_src_dels_in B L A mem HA h : src_at (rc := rc) B L A mem HA h -> incl (src_dels h) (blocks L A).
Proof.
  intros (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & PIN & _ & _ & _ & _ & LE & LH & _).
  assert (AR : forall LA l lines, list_at (rc := rc) B L A mem LA l lines -> incl (arr_sz l) (blocks L A)).
  { intros LA l lines (_ & _ & LV & _) t Ht. unfold arr_sz in Ht.
    revert Ht. destruct (Z.eqb_spec (hl_cap l) 0) as [C|C]; intros Ht; [destruct Ht|]. destruct Ht as [<-|[]].
    destruct LV as [(X & _)|(_ & X & _)]; [contradiction|exact X]. }
  intros t Ht. unfold src_dels in Ht. rewrite !in_app_iff in Ht.
  destruct Ht as [Ht|[[<-|[]]|[Ht|Ht]]]; [exact (AR _ _ _ LP t Ht)| |exact (AR _ _ _ LE t Ht)|exact (AR _ _ _ LH t Ht)].
  exact PIN.
Qed.

Lemma mv_eok B L A mem e : RelayRep.entry_ok (rc := rc) B L A mem e ->
  (re_cap e <> 0 -> In (re_buf e, re_cap e) (blocks L A) /\ 0 <= re_cap e) /\
  (re_hp e <> 0 -> In (re_hp e, re_kh e) (blocks L A) /\ 0 <= re_kh e).
Proof.
  intros (_ & _ & _ & _ & _ & C3 & _ & _ & _ & BC & _ & HC & _). split.
  - intros Hc. destruct BC as [(X & _)|(X1 & X2 & _)]; [contradiction|]. split; [exact X2|lia].
  - intros Hh. destruct HC as [(X & _)|(X1 & _ & _ & X4 & _)]; [contradiction|]. split; [exact X1|lia].
Qed.

Lemma mv_eok_nn B L A mem e : RelayRep.entry_ok (rc := rc) B L A mem e ->
  0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e).
Proof.
  intros H. pose proof H as (_ & _ & _ & _ & _ & C3 & _). destruct (mv_eok B L A mem e H) as (_ & H2).
  split; [lia|intros Hh; exact (proj2 (H2 Hh))].
Qed.

End Blk.

Lemma mv_scan V L A L' A' (recs : list Z) :
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 <= m) ->
  (forall t, In t (blocks L' A') <-> In t (blocks L A) /\ ~ In (fst t) recs) ->
  (forall q, In q recs -> ~ In q (rv_nc V)) ->
  nc_move V L A V L' A' [] [].
Proof.
  intros NK NP KB HP HR.
  apply (nc_move_mk V L A V L' A' [] [] (rv_nc V) [] (filter (fun t => existsb (Z.eqb (fst t)) recs) (blocks L A))).
  - exact NK.
  - exact NP.
  - cbn [map app]. rewrite app_nil_r. apply Permutation_refl.
  - cbn [map]. rewrite app_nil_r. apply Permutation_refl.
  - cbn [app]. apply mv_nd_mapfilter. exact NK.
  - constructor.
  - cbn [app]. intros t Ht. apply filter_In in Ht. exact (proj1 Ht).
  - intros t. cbn [app In]. rewrite (HP t), filter_In, mv_inb. split.
    + intros [H1 H2]. left. split; [exact H1|]. intros [_ H3]. exact (H2 H3).
    + intros [[H1 H2]|[]]. split; [exact H1|]. intros H3. exact (H2 (conj H1 H3)).
  - intros t [].
  - intros q m H. exact (KB q m (proj1 (proj1 (HP (q, m)) H))).
  - intros t [].
  - cbn [app]. intros t Ht. apply filter_In in Ht as [_ Ht]. apply mv_inb in Ht. exact (HR _ Ht).
  - intros g [].
Qed.

Lemma mv_reset L A L' A' G O (l1 l2 : list (hsrc * nat)) (y : hsrc * nat) (h : hsrc) :
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 <= m) ->
  incl (src_dels h) (blocks L A) -> List.NoDup (hs_blocks h) -> src_nc h = src_nc (fst y) ->
  (forall q, In q (hs_blocks h) ->
     q <> G /\ q <> O /\ ~ In q (concat (map (fun p => src_nc (fst p)) (l1 ++ l2)))) ->
  (forall t, In t (blocks L' A') <-> In t (blocks L A) /\ ~ In (fst t) (hs_blocks h)) ->
  nc_move (view_of G O [] (l1 ++ y :: l2)) L A (view_of G O [] (l1 ++ l2)) L' A' (src_dels h) [].
Proof.
  intros NK NP KB HD NH HS HQ HP.
  assert (SD : forall t, In t (src_dels h) -> In (fst t) (src_nc h)).
  { intros t Ht. rewrite <- mv_src_fst. apply in_map. exact Ht. }
  remember (filter (fun t => existsb (Z.eqb (fst t)) (hs_blocks h) && negb (existsb (Z.eqb (fst t)) (src_nc h)))
    (blocks L A)) as Y eqn:HY.
  assert (Yin : forall t, In t Y <-> In t (blocks L A) /\ In (fst t) (hs_blocks h) /\ ~ In (fst t) (src_nc h)).
  { intros t. rewrite HY, filter_In, andb_true_iff, negb_true_iff, mv_inb. split.
    - intros (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros X. apply mv_inb in X. congruence.
    - intros (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
      destruct (existsb (Z.eqb (fst t)) (src_nc h)) eqn:X; [apply mv_inb in X; contradiction|reflexivity]. }
  assert (DY : forall t, In t (src_dels h ++ Y) -> In (fst t) (hs_blocks h)).
  { intros t Ht. apply in_app_iff in Ht as [Ht|Ht]; [exact (mv_snc_hb _ _ (SD t Ht))|exact (proj1 (proj2 (proj1 (Yin t) Ht)))]. }
  assert (DYc : forall t, In t (blocks L A) -> In (fst t) (hs_blocks h) -> In t (src_dels h ++ Y)).
  { intros t Ht Hb. apply in_or_app. destruct (in_dec Z.eq_dec (fst t) (src_nc h)) as [X|X].
    - left. rewrite <- mv_src_fst in X. apply in_map_iff in X as (d & Ed & Hd).
      rewrite (mv_fst_eq (blocks L A) t d NK Ht (HD d Hd) (eq_sym Ed)). exact Hd.
    - right. apply Yin. split; [exact Ht|]. split; [exact Hb|exact X]. }
  apply (nc_move_mk _ _ _ _ _ _ _ _ (G :: O :: concat (map (fun p => src_nc (fst p)) (l1 ++ l2))) [] Y).
  - exact NK.
  - exact NP.
  - unfold view_of. cbn [rv_nc map concat app]. rewrite mv_src_fst, HS, !map_app, !concat_app. cbn [map concat].
    rewrite app_nil_r. apply perm_skip, perm_skip. rewrite <- app_assoc. apply Permutation_app_head.
    apply Permutation_app_comm.
  - unfold view_of. cbn [rv_nc map concat app]. rewrite app_nil_r. apply Permutation_refl.
  - rewrite map_app, mv_src_fst. apply mv_app; [exact (mv_snc_nd h NH)| |].
    + rewrite HY. exact (mv_nd_mapfilter _ _ NK).
    + intros q H1 H2. apply in_map_iff in H2 as (t & <- & Ht). exact (proj2 (proj2 (proj1 (Yin t) Ht)) H1).
  - constructor.
  - intros t Ht. apply in_app_iff in Ht as [Ht|Ht]; [exact (HD t Ht)|exact (proj1 (proj1 (Yin t) Ht))].
  - intros t. rewrite (HP t). cbn [In]. split.
    + intros [H1 H2]. left. split; [exact H1|]. intros X. exact (H2 (DY t X)).
    + intros [[H1 H2]|[]]. split; [exact H1|]. intros X. exact (H2 (DYc t H1 X)).
  - intros t [].
  - intros q m H. exact (KB q m (proj1 (proj1 (HP (q, m)) H))).
  - intros [q m] Ht. exact (KB q m (HD _ Ht)).
  - intros t Ht. destruct (HQ (fst t) (DY t Ht)) as (N1 & N2 & N3). intros [X|[X|X]].
    + exact (N1 (eq_sym X)).
    + exact (N2 (eq_sym X)).
    + exact (N3 X).
  - intros g [].
Qed.

Lemma mv_fin L A L' A' G OUT CAP es hj (live : bool) OUT' CAPp CAPr :
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 <= m /\ 4096 <= q) ->
  List.NoDup (target_addrs G OUT es hj) ->
  Forall (fun e => (re_cap e <> 0 -> In (re_buf e, re_cap e) (blocks L A) /\ 0 <= re_cap e) /\
                   (re_hp e <> 0 -> In (re_hp e, re_kh e) (blocks L A) /\ 0 <= re_kh e)) es ->
  0 <= CAP -> (CAP = 0 -> OUT = 0) -> (0 < CAP -> In (OUT, CAP) (blocks L A)) ->
  (live = false -> CAPr = CAP) ->
  (live = true -> CAPp = CAPr /\ 0 < CAPr /\
     forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (concat (map entry_blocks es)) -> 0 < m -> q <> OUT') ->
  (forall q m, In (q, m) (blocks L' A') <->
     ((In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (concat (map entry_blocks es))) \/
      (live = true /\ q = OUT' /\ m = CAPp) \/ (live = false /\ 0 < CAP /\ q = OUT /\ m = CAP))) ->
  nc_move (view_of G OUT es hj) L A (view_of G (if live then OUT' else OUT) [] hj) L' A'
    (out_move_dels OUT CAP (if live then OUT' else OUT) CAPr ++ ent_dels es)
    (out_move_adds OUT CAP (if live then OUT' else OUT) CAPr).
Proof.
  intros NK NP KB NT HE HC0 HC1 HC2 HNL HL HP.
  destruct (mv_target G OUT es hj NT) as (TGO & TGE & TGH & TOE & TOH & NDE & TEH).
  pose proof (mv_eb_perm es) as EBP.
  pose proof (Permutation_NoDup EBP NDE) as NDEK.
  assert (EBin : forall q, In q (concat (map entry_blocks es)) <-> In q (concat (map entry_nc es)) \/ In q (mv_ka es)).
  { intros q. rewrite <- in_app_iff. split; intros X;
      [eapply Permutation_in; [exact EBP|exact X]|eapply Permutation_in; [exact (Permutation_sym EBP)|exact X]]. }
  pose proof (mv_ent_blk L A es HE) as ENt.
  assert (ENf : forall t, In t (ent_dels es) -> In (fst t) (concat (map entry_nc es))).
  { intros t Ht. rewrite <- mv_ent_fst. apply in_map. exact Ht. }
  remember (filter (fun t => existsb (Z.eqb (fst t)) (mv_ka es)) (blocks L A)) as Y eqn:HY.
  assert (Yin : forall t, In t Y <-> In t (blocks L A) /\ In (fst t) (mv_ka es)).
  { intros t. rewrite HY, filter_In, mv_inb. tauto. }
  assert (NDY : List.NoDup (map fst Y)) by (rewrite HY; exact (mv_nd_mapfilter _ _ NK)).
  assert (EBb : forall q m, In (q, m) (blocks L A) -> In q (concat (map entry_blocks es)) ->
      In (q, m) (ent_dels es ++ Y)).
  { intros q m Hq Hb. apply in_or_app. apply EBin in Hb as [Hb|Hb].
    - left. rewrite <- mv_ent_fst in Hb. apply in_map_iff in Hb as (d & Ed & Hd).
      rewrite (mv_fst_eq (blocks L A) (q, m) d NK Hq (proj1 (ENt d Hd)) (eq_sym Ed)). exact Hd.
    - right. apply Yin. split; [exact Hq|exact Hb]. }
  assert (EDb : forall t, In t (ent_dels es ++ Y) -> In (fst t) (concat (map entry_blocks es))).
  { intros t Ht. apply EBin. apply in_app_iff in Ht as [Ht|Ht]; [left; exact (ENf t Ht)|right; exact (proj2 (proj1 (Yin t) Ht))]. }
  assert (EDK : forall t, In t (ent_dels es ++ Y) -> In t (blocks L A)).
  { intros t Ht. apply in_app_iff in Ht as [Ht|Ht]; [exact (proj1 (ENt t Ht))|exact (proj1 (proj1 (Yin t) Ht))]. }
  assert (NDD : List.NoDup (map fst (ent_dels es ++ Y))).
  { rewrite map_app, mv_ent_fst. apply mv_app; [exact (NoDup_app_remove_r _ _ NDEK)|exact NDY|].
    intros q H1 H2. apply in_map_iff in H2 as (t & <- & Ht). apply Yin in Ht as [_ Ht].
    exact (mv_disj _ _ _ NDEK H1 Ht). }
  assert (O0 : forall m, In (OUT, m) (blocks L A) -> 0 < CAP /\ m = CAP).
  { intros m Hm. destruct (Z.eq_dec CAP 0) as [C|C].
    - rewrite (HC1 C) in Hm. pose proof (KB 0 m Hm). lia.
    - assert (CP : 0 < CAP) by lia. split; [exact CP|].
      pose proof (mv_fst_eq (blocks L A) (OUT, m) (OUT, CAP) NK Hm (HC2 CP) eq_refl) as X. congruence. }
  assert (ESR : forall q, In q (concat (map entry_blocks es)) -> q <> G /\ q <> OUT /\
      ~ In q (concat (map (fun p => src_nc (fst p)) hj))).
  { intros q Hq. split; [intros ->; exact (TGE Hq)|]. split; [intros ->; exact (TOE Hq)|].
    intros X. exact (TEH q Hq (mv_sr_hb hj q X)). }
  remember (if live then OUT' else OUT) as q1 eqn:Hq1.
  destruct (out_same OUT CAP q1 CAPr) eqn:KS.
  - assert (Q1 : q1 = OUT /\ CAPr = CAP).
    { unfold out_same in KS. apply andb_prop in KS as [K1 K2]. apply Z.eqb_eq in K1, K2. split; assumption. }
    destruct Q1 as (Q1 & C1).
    assert (QL : live = true -> OUT' = OUT) by (intros LV; rewrite LV in Hq1; cbn in Hq1; congruence).
    assert (OD : out_move_dels OUT CAP q1 CAPr = []) by (unfold out_move_dels; rewrite KS; reflexivity).
    assert (AD : out_move_adds OUT CAP q1 CAPr = []) by (unfold out_move_adds; rewrite KS; reflexivity).
    rewrite OD, AD, app_nil_l, Q1.
    apply (nc_move_mk _ _ _ _ _ _ _ _ (G :: OUT :: concat (map (fun p => src_nc (fst p)) hj)) [] Y).
    + exact NK.
    + exact NP.
    + unfold view_of. cbn [rv_nc app]. rewrite mv_ent_fst, app_nil_r. apply perm_skip, perm_skip.
      apply Permutation_app_comm.
    + unfold view_of. cbn [rv_nc map concat app]. rewrite app_nil_r. apply Permutation_refl.
    + exact NDD.
    + constructor.
    + exact EDK.
    + intros [q m]. rewrite (HP q m). cbn [In fst]. split.
      * intros [(H0 & No & Ne)|[(Hl & Eq & Em)|(Hl & Hc & Eq & Em)]].
        -- left. split; [exact H0|]. intros X. exact (Ne (EDb _ X)).
        -- left. subst q m. destruct (HL Hl) as (E1 & E2 & _). rewrite (QL Hl), E1, C1.
           assert (CP : 0 < CAP) by lia. split; [exact (HC2 CP)|]. intros X. exact (TOE (EDb _ X)).
        -- left. subst q m. split; [exact (HC2 Hc)|]. intros X. exact (TOE (EDb _ X)).
      * intros [(H0 & Nd)|[]]. destruct (Z.eq_dec q OUT) as [->|No].
        -- destruct (O0 m H0) as (CP & ->). right. destruct live eqn:LV.
           ++ left. destruct (HL eq_refl) as (E1 & _ & _). split; [reflexivity|].
              split; [exact (eq_sym (QL eq_refl))|lia].
           ++ right. split; [reflexivity|]. split; [exact CP|split; reflexivity].
        -- left. split; [exact H0|]. split; [exact No|]. intros X. exact (Nd (EBb q m H0 X)).
    + intros t [].
    + intros q m H. apply HP in H as [(H0 & _)|[(Hl & _ & ->)|(_ & Hc & _ & ->)]];
        [exact (proj1 (KB q m H0))|destruct (HL Hl) as (E1 & E2 & _); lia|lia].
    + intros t Ht. exact (proj2 (ENt t Ht)).
    + intros t Ht. destruct (ESR (fst t) (EDb t Ht)) as (N1 & N2 & N3). intros [X|[X|X]].
      * exact (N1 (eq_sym X)).
      * exact (N2 (eq_sym X)).
      * exact (N3 X).
    + intros g [].
  - assert (LV : live = true).
    { destruct live eqn:LV; [reflexivity|]. exfalso. cbn in Hq1. subst q1. unfold out_same in KS.
      rewrite (HNL eq_refl), !Z.eqb_refl in KS. discriminate KS. }
    destruct (HL LV) as (EC & CP & HQ). rewrite LV in Hq1. cbn in Hq1.
    assert (OD : out_move_dels OUT CAP q1 CAPr = if CAP =? 0 then [] else [(OUT, CAP)])
      by (unfold out_move_dels; rewrite KS; reflexivity).
    assert (AD : out_move_adds OUT CAP q1 CAPr = [(q1, CAPr)]) by (unfold out_move_adds; rewrite KS; reflexivity).
    rewrite OD, AD.
    assert (ODf : forall t, In t (if CAP =? 0 then [] else [(OUT, CAP)]) -> t = (OUT, CAP) /\ 0 < CAP).
    { intros t Ht. revert Ht. destruct (Z.eqb_spec CAP 0) as [C|C]; intros Ht; [destruct Ht|].
      destruct Ht as [<-|[]]. split; [reflexivity|lia]. }
    assert (DYf : forall t, In t (((if CAP =? 0 then [] else [(OUT, CAP)]) ++ ent_dels es) ++ Y) ->
        fst t = OUT \/ In (fst t) (concat (map entry_blocks es))).
    { intros t Ht. rewrite <- app_assoc in Ht.
      apply in_app_iff in Ht as [Ht|Ht]; [left; rewrite (proj1 (ODf t Ht)); reflexivity|right; exact (EDb t Ht)]. }
    assert (DYm : forall q m, In (q, m) (blocks L A) -> q = OUT \/ In q (concat (map entry_blocks es)) ->
        In (q, m) (((if CAP =? 0 then [] else [(OUT, CAP)]) ++ ent_dels es) ++ Y)).
    { intros q m Hq [->|Hb]; rewrite <- app_assoc.
      - destruct (O0 m Hq) as (CPo & ->). apply in_or_app. left.
        rewrite (proj2 (Z.eqb_neq CAP 0) ltac:(lia)). left. reflexivity.
      - apply in_or_app. right. exact (EBb q m Hq Hb). }
    apply (nc_move_mk _ _ _ _ _ _ _ _ (G :: concat (map (fun p => src_nc (fst p)) hj))
             (if CAP =? 0 then [OUT] else []) Y).
    + exact NK.
    + exact NP.
    + unfold view_of. cbn [rv_nc]. rewrite map_app, mv_ent_fst, <- app_comm_cons. apply perm_skip.
      apply (Permutation_count_occ Z.eq_dec). intros x.
      assert (OG : @eq nat (count_occ Z.eq_dec [OUT] x)
          (Nat.add (count_occ Z.eq_dec (map fst (if CAP =? 0 then [] else [(OUT, CAP)])) x)
                   (count_occ Z.eq_dec (if CAP =? 0 then [OUT] else []) x))).
      { destruct (CAP =? 0); cbn [map fst]; rewrite ?count_occ_nil; lia. }
      change (OUT :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj)) with
        ([OUT] ++ concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj)).
      rewrite !count_occ_app. lia.
    + unfold view_of. cbn [rv_nc map concat app fst]. apply perm_skip. apply Permutation_cons_append.
    + rewrite <- app_assoc, map_app. apply mv_app.
      * destruct (CAP =? 0); cbn [map fst]; repeat constructor. intros [].
      * exact NDD.
      * intros q H1 H2. apply in_map_iff in H1 as (t & <- & Ht). destruct (ODf t Ht) as (-> & _). cbn [fst] in H2.
        apply in_map_iff in H2 as (u & Eu & Hu). apply TOE. rewrite <- Eu. exact (EDb u Hu).
    + repeat constructor. intros [].
    + intros t Ht. rewrite <- app_assoc in Ht.
      apply in_app_iff in Ht as [Ht|Ht]; [destruct (ODf t Ht) as (-> & CPo); exact (HC2 CPo)|exact (EDK t Ht)].
    + intros [q m]. rewrite (HP q m). cbn [In]. split.
      * intros [(H0 & No & Ne)|[(_ & Eq & Em)|(Hl & _)]].
        -- left. split; [exact H0|]. intros X. destruct (DYf _ X) as [X1|X1]; [exact (No X1)|exact (Ne X1)].
        -- right. left. subst q m. rewrite Hq1, EC. reflexivity.
        -- rewrite LV in Hl. discriminate Hl.
      * intros [(H0 & Nd)|[Eq|[]]].
        -- left. split; [exact H0|]. split; [intros X; exact (Nd (DYm q m H0 (or_introl X)))|].
           intros X. exact (Nd (DYm q m H0 (or_intror X))).
        -- right. left. injection Eq as <- <-. split; [exact LV|]. split; [exact Hq1|exact (eq_sym EC)].
    + intros t [<-|[]] Hk. apply DYm; [exact Hk|]. cbn [fst]. rewrite Hq1.
      destruct (Z.eq_dec OUT' OUT) as [X|X]; [left; exact X|].
      destruct (in_dec Z.eq_dec OUT' (concat (map entry_blocks es))) as [Y1|Y1]; [right; exact Y1|].
      rewrite Hq1 in Hk. exfalso. exact (HQ OUT' CAPr Hk X Y1 CP eq_refl).
    + intros q m H. apply HP in H as [(H0 & _)|[(_ & _ & ->)|(Hl & _)]];
        [exact (proj1 (KB q m H0))|rewrite EC; lia|rewrite LV in Hl; discriminate Hl].
    + intros t Ht. apply in_app_iff in Ht as [Ht|Ht]; [destruct (ODf t Ht) as (-> & _); cbn [snd]; lia|exact (proj2 (ENt t Ht))].
    + intros t Ht. destruct (DYf t Ht) as [X|X].
      * rewrite X. intros [Y1|Y1]; [exact (TGO Y1)|exact (TOH (mv_sr_hb hj _ Y1))].
      * destruct (ESR (fst t) X) as (N1 & _ & N3). intros [Y1|Y1]; [exact (N1 (eq_sym Y1))|exact (N3 Y1)].
    + intros g Hg. revert Hg. destruct (Z.eqb_spec CAP 0) as [C|C]; intros Hg m Hm; [|destruct Hg].
      destruct Hg as [<-|[]]. rewrite (HC1 C) in Hm. pose proof (KB 0 m Hm). lia.
Qed.

Definition exit_res_fin_d (F : ResFormT) (RI : res_inv) (CS : list byte -> list Z) : Prop :=
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall k L A cl br dd G (mx cap out : word) es hj,
      RI E k (view_of G (bv_unsigned out) es hj) L A -> List.NoDup (map fst (blocks L A)) ->
      Forall (fun e => 0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e)) es ->
      entries_total es < INPUT_MAX ->
      res_tr F (fin_RV_d RI E k L A G (bv_unsigned out) es hj (send_live cl br dd (entries_total es))
                  (bv_unsigned mx) (bv_unsigned cap))
        A (relay_finish_tr (known_at L A) (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0 (bv_unsigned cap)
             es 0 (known_at L A (bv_unsigned out))).

Theorem exit_res_fin_reply_d : exit_res_fin_d pack3_form RI3_reply CS_reply.
Proof.
  intros B API LS SH SK ra empty rc fx j E HF k L A cl br dd G mx cap out es hj HRI HND Hes Htot.
  pose proof (bv_unsigned_in_range _ cap) as [HCAP _]. pose proof (bv_unsigned_in_range _ mx) as [HMX _].
  exact (fin_res3 E k L A G (bv_unsigned out) es hj _ (bv_unsigned mx) (bv_unsigned cap) HRI HND HMX HCAP Hes Htot).
Qed.
