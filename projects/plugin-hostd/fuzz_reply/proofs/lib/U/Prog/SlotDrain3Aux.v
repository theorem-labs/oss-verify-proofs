From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT SlotKept SlotPack
  AllocPack AllocPackRoom AllocBound AllocPack3 AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotInv SlotParse SlotCaps3 SlotRI3
  RelayRunT RelayRunF RelayRep HarnessRep RelayModel SlotRun3 SlotP5R3G.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition bkc (g : list (Z * adrF)) (c : Z) : Z := zsum (fun p => ncb (fst p) c) g.

Definition bkb (g : list (Z * adrF)) : Z := zsum (fun p => fst p) g.

Definition bks (qs : list sptr) (g : list (Z * adrF)) : list sptr :=
  flat_map (fun p => slot3 (fst p) (resolveF qs (snd p))) g.

Definition bnd (g : list (Z * adrF)) (mxs : list Z) : Prop := Forall2 (fun p m => 0 <= fst p <= m) g mxs.

Definition mi (qs Ss : list sptr) (g : list (Z * adrF)) (M : list (sptr * Z)) : Prop :=
  List.NoDup (map fst M) /\ incl (map fst M) (bks qs g ++ Ss).

Inductive steps (mxs : list Z) : nat -> list (Z * adrF) -> trF -> list (Z * adrF) -> list Z -> Prop :=
| sp_nil j g : steps mxs j g [] g []
| sp_copy j g n t g' u : 0 <= n <= NMAX -> steps mxs (S j) g t g' u -> steps mxs j g (RMalloc n :: t) g' (n :: u)
| sp_free j g n a t g' u : 0 <= n -> steps mxs j g t g' u -> steps mxs j g (RFree n a :: t) g' u
| sp_grow j ga gb k a n t g' u : 0 < n <= NMAX -> n <= nth (length ga) mxs 0 ->
    steps mxs (S j) (ga ++ (n, Ret j) :: gb) t g' u ->
    steps mxs j (ga ++ (k, a) :: gb) ((if k =? 0 then RMalloc n else RRealloc k n a) :: t) g' u.

Lemma sp_grow0 mxs j gb k a n t g' u : 0 < n <= NMAX -> n <= nth 0 mxs 0 ->
  steps mxs (S j) ((n, Ret j) :: gb) t g' u ->
  steps mxs j ((k, a) :: gb) ((if k =? 0 then RMalloc n else RRealloc k n a) :: t) g' u.
Proof. exact (sp_grow mxs j [] gb k a n t g' u). Qed.

Lemma sp_grow1 mxs j x0 gb k a n t g' u : 0 < n <= NMAX -> n <= nth 1 mxs 0 ->
  steps mxs (S j) (x0 :: (n, Ret j) :: gb) t g' u ->
  steps mxs j (x0 :: (k, a) :: gb) ((if k =? 0 then RMalloc n else RRealloc k n a) :: t) g' u.
Proof. exact (sp_grow mxs j [x0] gb k a n t g' u). Qed.

Lemma sp_grow2 mxs j x0 x1 gb k a n t g' u : 0 < n <= NMAX -> n <= nth 2 mxs 0 ->
  steps mxs (S j) (x0 :: x1 :: (n, Ret j) :: gb) t g' u ->
  steps mxs j (x0 :: x1 :: (k, a) :: gb) ((if k =? 0 then RMalloc n else RRealloc k n a) :: t) g' u.
Proof. exact (sp_grow mxs j [x0; x1] gb k a n t g' u). Qed.

Lemma sp_grow3 mxs j x0 x1 x2 gb k a n t g' u : 0 < n <= NMAX -> n <= nth 3 mxs 0 ->
  steps mxs (S j) (x0 :: x1 :: x2 :: (n, Ret j) :: gb) t g' u ->
  steps mxs j (x0 :: x1 :: x2 :: (k, a) :: gb) ((if k =? 0 then RMalloc n else RRealloc k n a) :: t) g' u.
Proof. exact (sp_grow mxs j [x0; x1; x2] gb k a n t g' u). Qed.

Lemma nret_cons (e : RelayRunT.rev sptr) (t : trF) : nretF (e :: t) = (rets sptr e + nretF t)%nat.
Proof. reflexivity. Qed.

Lemma steps_app mxs j g t1 g1 u1 t2 g2 u2 : steps mxs j g t1 g1 u1 -> steps mxs (j + nretF t1) g1 t2 g2 u2 ->
  steps mxs j g (t1 ++ t2) g2 (u1 ++ u2).
Proof.
  intros H. revert t2 g2 u2.
  induction H as [j g|j g n t g' u Hn Hs IH|j g n a t g' u Hn Hs IH|j ga gb k a n t g' u Hn Hm Hs IH];
    intros t2 g2 u2 H2; cbn [app].
  - rewrite Nat.add_0_r in H2. exact H2.
  - apply sp_copy; [exact Hn|]. apply IH. rewrite nret_cons in H2. cbn [rets] in H2.
    replace (S j + nretF t)%nat with (j + S (nretF t))%nat by lia. exact H2.
  - apply sp_free; [exact Hn|]. apply IH. rewrite nret_cons in H2. cbn [rets] in H2. exact H2.
  - apply sp_grow; [exact Hn|exact Hm|]. apply IH. rewrite nret_cons in H2.
    replace (rets sptr (if k =? 0 then RMalloc n else RRealloc k n a)) with 1%nat in H2
      by (destruct (k =? 0); reflexivity).
    replace (S j + nretF t)%nat with (j + (1 + nretF t))%nat by lia. exact H2.
Qed.

Lemma steps_len mxs j g t g' u : steps mxs j g t g' u -> length g' = length g.
Proof.
  induction 1 as [j g|j g n t g' u Hn Hs IH|j g n a t g' u Hn Hs IH|j ga gb k a n t g' u Hn Hm Hs IH];
    [reflexivity|exact IH|exact IH|].
  rewrite IH, !length_app. reflexivity.
Qed.

Lemma steps_u mxs j g t g' u : steps mxs j g t g' u -> Forall (fun n => 0 <= n) u.
Proof.
  induction 1 as [j g|j g n t g' u Hn Hs IH|j g n a t g' u Hn Hs IH|j ga gb k a n t g' u Hn Hm Hs IH];
    [constructor|constructor; [lia|exact IH]|exact IH|exact IH].
Qed.

Lemma bnd_upd ga gb k a n q mxs : bnd (ga ++ (k, a) :: gb) mxs -> 0 <= n <= nth (length ga) mxs 0 ->
  bnd (ga ++ (n, q) :: gb) mxs.
Proof.
  unfold bnd. intros H Hn. apply Forall2_app_inv_l in H as (l1 & l2 & H1 & H2 & ->).
  inversion H2 as [|x m y l2' Hx Hr]; subst.
  rewrite (Forall2_length H1), nth_middle in Hn.
  apply Forall2_app; [exact H1|]. constructor; [cbn [fst]; lia|exact Hr].
Qed.

Lemma bnd_nonneg g mxs : bnd g mxs -> Forall (fun p => 0 <= fst p) g.
Proof. unfold bnd. induction 1 as [|x y l l' Hx Hr IH]; constructor; [lia|exact IH]. Qed.

Lemma bnd_bkb g mxs : bnd g mxs -> bkb g <= zsum (fun m => m) mxs.
Proof.
  unfold bnd, bkb. induction 1 as [|x y l l' Hx Hr IH]; [cbn; lia|]. rewrite !zsum_cons. cbv beta. lia.
Qed.

Lemma bnd_mid ga gb k a mxs : bnd (ga ++ (k, a) :: gb) mxs -> 0 <= k.
Proof.
  intros H. apply bnd_nonneg in H. apply Forall_app in H as [_ H]. apply Forall_cons_iff in H as [H _]. exact H.
Qed.

Lemma steps_bnd mxs j g t g' u : steps mxs j g t g' u -> bnd g mxs -> bnd g' mxs.
Proof.
  induction 1 as [j g|j g n t g' u Hn Hs IH|j g n a t g' u Hn Hs IH|j ga gb k a n t g' u Hn Hm Hs IH];
    intros HB; [exact HB|exact (IH HB)|exact (IH HB)|].
  apply IH. apply (bnd_upd ga gb k a); [exact HB|lia].
Qed.

Lemma ncb_b n c : 0 <= ncb n c <= 1.
Proof. unfold ncb. destruct (n =? 0); [lia|apply one_if_b]. Qed.

Lemma ncb_pos n c : n <> 0 -> ncb n c = one_if c (band n).
Proof. intros H. unfold ncb. destruct (Z.eqb_spec n 0); [contradiction|reflexivity]. Qed.

Lemma bkc_b g c : 0 <= bkc g c <= Z.of_nat (length g).
Proof.
  unfold bkc. induction g as [|p g IH]; [cbn; lia|]. rewrite zsum_cons. cbv beta. cbn [length].
  pose proof (ncb_b (fst p) c). lia.
Qed.

Lemma bkc_upd ga gb k a n q c : bkc (ga ++ (n, q) :: gb) c = bkc (ga ++ (k, a) :: gb) c - ncb k c + ncb n c.
Proof. unfold bkc. rewrite !zsum_app, !zsum_cons. cbv beta. cbn [fst]. lia. Qed.

Lemma bkb_upd ga gb k a n q : bkb (ga ++ (n, q) :: gb) = bkb (ga ++ (k, a) :: gb) - k + n.
Proof. unfold bkb. rewrite !zsum_app, !zsum_cons. cbv beta. cbn [fst]. lia. Qed.

Lemma bks_mid qs ga gb k a : bks qs (ga ++ (k, a) :: gb) = bks qs ga ++ slot3 k (resolveF qs a) ++ bks qs gb.
Proof. unfold bks. rewrite flat_map_app. reflexivity. Qed.

Lemma slot3_le1 n x : (length (slot3 n x) <= 1)%nat.
Proof. unfold slot3. destruct (n =? 0); cbn [length]; lia. Qed.

Lemma bks_len qs g : (length (bks qs g) <= length g)%nat.
Proof.
  unfold bks. induction g as [|p g IH]; [cbn; lia|]. cbn [flat_map]. rewrite length_app. cbn [length].
  pose proof (slot3_le1 (fst p) (resolveF qs (snd p))). lia.
Qed.

Lemma steps_eff mxs j g t g' u : steps mxs j g t g' u -> Forall (fun p => 0 <= fst p) g ->
  Forall ev_ok t /\ (forall c, tr_dl t c <= bkc g' c - bkc g c + bcnt c u) /\
  tr_db t <= bkb g' - bkb g + zsum (fun n => n) u.
Proof.
  induction 1 as [j g|j g n t g' u Hn Hs IH|j g n a t g' u Hn Hs IH|j ga gb k a n t g' u Hn Hm Hs IH];
    intros HG.
  - split; [constructor|]. split; [intros c; change (tr_dl [] c) with 0; change (bcnt c []) with 0; lia|].
    change (tr_db []) with 0. change (zsum (fun n => n) []) with 0. lia.
  - destruct (IH HG) as (O & D & B). split; [constructor; [cbn [ev_ok]; lia|exact O]|]. unfold tr_dl, tr_db in *.
    split; [intros c; rewrite zsum_cons, bcnt_cons; specialize (D c); cbn [ev_dl]; lia|].
    rewrite !zsum_cons. cbn [ev_db]. lia.
  - destruct (IH HG) as (O & D & B). split; [constructor; [cbn [ev_ok]; lia|exact O]|]. unfold tr_dl, tr_db in *.
    split; [intros c; rewrite zsum_cons; specialize (D c); cbn [ev_dl]; pose proof (one_if_b c (band n)); lia|].
    rewrite zsum_cons. cbn [ev_db]. lia.
  - assert (Hk : 0 <= k).
    { apply Forall_app in HG as [_ HG]. apply Forall_cons_iff in HG as [HG _]. exact HG. }
    assert (HG' : Forall (fun p => 0 <= fst p) (ga ++ (n, Ret j) :: gb)).
    { apply Forall_app in HG as [H1 H2]. apply Forall_cons_iff in H2 as [_ H2].
      apply Forall_app. split; [exact H1|]. constructor; [cbn [fst]; lia|exact H2]. }
    destruct (IH HG') as (O & D & B). unfold tr_dl, tr_db in *.
    rewrite (bkb_upd ga gb k a n (Ret j)) in B.
    assert (Dc : forall c, zsum (fun e => ev_dl e c) t <=
                           bkc g' c - (bkc (ga ++ (k, a) :: gb) c - ncb k c + one_if c (band n)) + bcnt c u).
    { intros c. rewrite <- (ncb_pos n c) by lia. rewrite <- (bkc_upd ga gb k a n (Ret j)). apply D. }
    destruct (Z.eqb_spec k 0) as [Ek|Ek].
    + subst k. split; [constructor; [cbn [ev_ok]; lia|exact O]|].
      split; [intros c; rewrite zsum_cons; specialize (Dc c); cbn [ev_dl]; change (ncb 0 c) with 0 in Dc; lia|].
      rewrite zsum_cons. cbn [ev_db]. lia.
    + split; [constructor; [cbn [ev_ok]; lia|exact O]|].
      split; [intros c; rewrite zsum_cons; specialize (Dc c); rewrite (ncb_pos k) in Dc by exact Ek; cbn [ev_dl]; lia|].
      rewrite zsum_cons. cbn [ev_db]. lia.
Qed.

Lemma nodup_fst_filter (f : sptr * Z -> bool) M : List.NoDup (map fst M) -> List.NoDup (map fst (filter f M)).
Proof.
  induction M as [|e M IH]; intros H; [constructor|]. cbn [map] in H. apply List.NoDup_cons_iff in H as [H1 H2].
  cbn [filter]. destruct (f e); [|exact (IH H2)]. cbn [map]. constructor; [|exact (IH H2)].
  intros Hin. apply H1. apply in_map_iff in Hin as (e' & E & Hin). apply filter_In in Hin as [Hin _].
  rewrite <- E. apply in_map. exact Hin.
Qed.

Lemma incl_fst_filter (f : sptr * Z -> bool) M : incl (map fst (filter f M)) (map fst M).
Proof.
  intros x Hx. apply in_map_iff in Hx as (e & <- & Hin). apply filter_In in Hin as [Hin _]. apply in_map. exact Hin.
Qed.

Lemma mis_del_ne M p x : In x (map fst (mis_del M p)) -> x <> p.
Proof.
  unfold mis_del. intros Hx. apply in_map_iff in Hx as (e & <- & Hin). apply filter_In in Hin as [_ Hf].
  cbv beta in Hf. intros E. rewrite E, sptr_eqb_refl in Hf. cbn in Hf. discriminate Hf.
Qed.

Lemma mi_del qs Ss g M p : mi qs Ss g M -> mi qs Ss g (mis_del M p).
Proof.
  intros [HN HI]. unfold mis_del. split; [apply nodup_fst_filter; exact HN|].
  intros x Hx. apply HI. exact (incl_fst_filter _ M x Hx).
Qed.

Lemma mi_realloc M k n p q X Y : List.NoDup (map fst M) -> incl (map fst M) (X ++ p :: Y) ->
  List.NoDup (map fst (mis_realloc M k n p q)) /\ incl (map fst (mis_realloc M k n p q)) (X ++ q :: Y).
Proof.
  intros HN HI.
  assert (D : incl (map fst (mis_del M p)) (X ++ q :: Y)).
  { intros x Hx. pose proof (mis_del_ne M p x Hx) as Hne. unfold mis_del in Hx.
    apply incl_fst_filter in Hx. apply HI in Hx. apply in_app_or in Hx as [Hx|[Hx|Hx]].
    - apply in_or_app. left. exact Hx.
    - congruence.
    - apply in_or_app. right. right. exact Hx. }
  assert (DN : List.NoDup (map fst (mis_del M p))) by (unfold mis_del; apply nodup_fst_filter; exact HN).
  unfold mis_realloc. match goal with |- context [if ?t then _ else _] => destruct t eqn:E end.
  - apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _]. apply sptr_eqb_eq in E. subst q.
    cbn [map fst]. split.
    + constructor; [|exact DN]. intros Hx. exact (mis_del_ne M p p Hx eq_refl).
    + intros x [<-|Hx]; [apply in_or_app; right; left; reflexivity|exact (D x Hx)].
  - split; [exact DN|exact D].
Qed.

Lemma count_mis_le M c : count_mis M c <= Z.of_nat (length (map fst M)).
Proof. unfold count_mis. rewrite length_map. pose proof (filter_len_le (fun e : sptr * Z => snd e =? c) M). lia. Qed.

Lemma mi_count qs Ss g M c : mi qs Ss g M -> (length g + length Ss <= NC_MAX)%nat -> count_mis M c + 1 <= MC_ONE.
Proof.
  intros [HN HI] HL. pose proof (List.NoDup_incl_length HN HI) as L. rewrite length_app in L.
  pose proof (bks_len qs g). pose proof (count_mis_le M c). unfold MC_ONE, NC_MAX in *. lia.
Qed.

Lemma steps_room mxs qs Ss j g t g' u : steps mxs j g t g' u -> forall b1,
  bnd g mxs -> length (p3_live b1) = 49%nat -> (length g + length Ss <= NC_MAX)%nat ->
  CAPOK2 (GALL3 (p3_cap b1) (p3_mcap b1)) (GMAP3 (p3_cap b1) (p3_mcap b1)) BMAX NMAX ->
  (forall c, 0 <= c < 49 -> MC_ONE <= znth c (p3_mcap b1)) ->
  mi qs Ss g (p3_mis b1) ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b1) - bkc g c + Z.of_nat (length g) + 1 + bcnt c u <= znth c (p3_cap b1)) ->
  p3_bytes b1 - bkb g + zsum (fun m => m) mxs + NMAX + zsum (fun n => n) u <= BMAX ->
  room3 qs b1 j t /\ mi qs Ss g' (p3_mis (run3 qs b1 j t)).
Proof.
  induction 1 as [j g|j g n t g' u Hn Hs IH|j g n a t g' u Hn Hs IH|j ga gb k a n t g' u Hn Hm Hs IH];
    intros b1 HB HL HG HC HMC HMI HLv HBy.
  - split; [exact I|exact HMI].
  - pose proof (steps_u _ _ _ _ _ _ Hs) as HU. pose proof (zsum_id_nonneg u HU) as ZU.
    pose proof (bnd_bkb g mxs HB) as BK. pose proof (band_range n ltac:(lia)) as Bn.
    rewrite zsum_cons in HBy. cbv beta in HBy.
    assert (R : room_pack3 b1 n).
    { apply (room_pack3_of b1 n BMAX NMAX); [exact HC|lia|lia| |].
      - specialize (HLv (band n) ltac:(lia)). rewrite bcnt_cons in HLv. pose proof (bkc_b g (band n)).
        pose proof (bcnt_nonneg (band n) u). pose proof (one_if_b (band n) (band n)). lia.
      - intros Hb. pose proof (mi_count qs Ss g (p3_mis b1) (band n + 1) HMI HG). pose proof (HMC (band n + 1) ltac:(lia)).
        lia. }
    cbn [room_from run_from]. destruct (IH (pb3_malloc b1 n)) as [R1 R2].
    + exact HB.
    + unfold pb3_malloc. cbn [p3_live]. rewrite lv_add_length. exact HL.
    + exact HG.
    + exact HC.
    + exact HMC.
    + exact HMI.
    + intros c Hc. unfold pb3_malloc. cbn [p3_live p3_cap]. rewrite znth_lv_add_d by (first [exact HL|lia]).
      specialize (HLv c Hc). rewrite bcnt_cons in HLv. lia.
    + unfold pb3_malloc. cbn [p3_bytes]. lia.
    + split; [split; [exact R|exact R1]|exact R2].
  - pose proof (band_range n Hn) as Bn. cbn [room_from run_from].
    apply IH.
    + exact HB.
    + unfold pb3_free. cbn [p3_live]. rewrite lv_add_length. exact HL.
    + exact HG.
    + exact HC.
    + exact HMC.
    + unfold pb3_free. cbn [p3_mis]. apply mi_del. exact HMI.
    + intros c Hc. unfold pb3_free. cbn [p3_live p3_cap]. rewrite znth_lv_add_d by (first [exact HL|lia]).
      specialize (HLv c Hc). pose proof (one_if_b c (band n)). lia.
    + unfold pb3_free. cbn [p3_bytes]. lia.
  - pose proof (steps_u _ _ _ _ _ _ Hs) as HU. pose proof (zsum_id_nonneg u HU) as ZU.
    pose proof (bnd_bkb _ mxs HB) as BK. pose proof (band_range n ltac:(lia)) as Bn.
    pose proof (bnd_mid ga gb k a mxs HB) as Hk. pose proof (band_range k Hk) as Bk.
    assert (HB' : bnd (ga ++ (n, Ret j) :: gb) mxs) by (apply (bnd_upd ga gb k a); [exact HB|lia]).
    assert (HG' : (length (ga ++ (n, Ret j) :: gb) + length Ss <= NC_MAX)%nat)
      by (rewrite !length_app in *; cbn [length] in *; exact HG).
    assert (EL : Z.of_nat (length (ga ++ (n, Ret j) :: gb)) = Z.of_nat (length (ga ++ (k, a) :: gb)))
      by (rewrite !length_app; reflexivity).
    assert (R : room_pack3 b1 n).
    { apply (room_pack3_of b1 n BMAX NMAX); [exact HC|lia|lia| |].
      - specialize (HLv (band n) ltac:(lia)). pose proof (bkc_b (ga ++ (k, a) :: gb) (band n)).
        pose proof (bcnt_nonneg (band n) u). lia.
      - intros Hb. pose proof (mi_count qs Ss _ (p3_mis b1) (band n + 1) HMI HG). pose proof (HMC (band n + 1) ltac:(lia)).
        lia. }
    assert (Sn : slot3 n (resolveF qs (Ret j)) = [nth j qs (SP 0 0)])
      by (unfold slot3; rewrite (proj2 (Z.eqb_neq n 0)) by lia; reflexivity).
    destruct (Z.eqb_spec k 0) as [Ek|Ek].
    + subst k. cbn [room_from run_from]. destruct (IH (pb3_malloc b1 n)) as [R1 R2].
      * exact HB'.
      * unfold pb3_malloc. cbn [p3_live]. rewrite lv_add_length. exact HL.
      * exact HG'.
      * exact HC.
      * exact HMC.
      * destruct HMI as [HN HI]. split; [exact HN|]. unfold pb3_malloc. cbn [p3_mis].
        intros x Hx. specialize (HI x Hx). rewrite bks_mid in HI |- *. rewrite Sn.
        unfold slot3 in HI. rewrite Z.eqb_refl in HI. rewrite !in_app_iff in HI |- *. cbn [In] in HI |- *.
        rewrite ?in_app_iff in HI |- *. tauto.
      * intros c Hc. unfold pb3_malloc. cbn [p3_live p3_cap]. rewrite znth_lv_add_d by (first [exact HL|lia]).
        rewrite (bkc_upd ga gb 0 a n (Ret j) c), (ncb_pos n) by lia. rewrite EL. specialize (HLv c Hc).
        change (ncb 0 c) with 0. lia.
      * unfold pb3_malloc. cbn [p3_bytes]. rewrite (bkb_upd ga gb 0 a n (Ret j)). lia.
      * split; [split; [exact R|exact R1]|exact R2].
    + cbn [room_from run_from].
      destruct (IH (pb3_realloc b1 k n (resolveF qs a) (nth j qs (SP 0 0)))) as [R1 R2].
      * exact HB'.
      * unfold pb3_realloc. cbn [p3_live]. rewrite !lv_add_length. exact HL.
      * exact HG'.
      * exact HC.
      * exact HMC.
      * destruct HMI as [HN HI]. unfold pb3_realloc. cbn [p3_mis].
        assert (HI' : incl (map fst (p3_mis b1)) (bks qs ga ++ resolveF qs a :: (bks qs gb ++ Ss))).
        { intros x Hx. specialize (HI x Hx). rewrite bks_mid in HI. unfold slot3 in HI.
          rewrite (proj2 (Z.eqb_neq k 0) Ek) in HI. rewrite <- !app_assoc in HI. exact HI. }
        destruct (mi_realloc (p3_mis b1) k n (resolveF qs a) (nth j qs (SP 0 0)) _ _ HN HI') as [N2 I2].
        split; [exact N2|]. intros x Hx. specialize (I2 x Hx). rewrite bks_mid, Sn, <- !app_assoc. exact I2.
      * intros c Hc. unfold pb3_realloc. cbn [p3_live p3_cap].
        rewrite znth_lv_add_d by (first [rewrite lv_add_length; exact HL|lia]).
        rewrite znth_lv_add_d by (first [exact HL|lia]).
        rewrite (bkc_upd ga gb k a n (Ret j) c), (ncb_pos n) by lia. rewrite (ncb_pos k c Ek). rewrite EL.
        specialize (HLv c Hc). lia.
      * unfold pb3_realloc. cbn [p3_bytes]. rewrite (bkb_upd ga gb k a n (Ret j)). lia.
      * split; [split; [exact R|exact R1]|exact R2].
Qed.

Definition ek1 (l : list Z) : list Z :=
  match gesture l with Some (GBegin, x) => [Z.of_nat (length x) + 1] | _ => [] end.

Definition ekl (ls : list (list Z)) : list Z := concat (map ek1 ls).

Definition rcl (ls : list (list Z)) : list Z := map (fun l => zlen l + 1) ls.

Definition chg (u : list Z) (L : list (list Z)) : Prop :=
  (forall c, bcnt c u <= bcnt c (rcl L) + bcnt c (ekl L)) /\
  zsum (fun n => n) u <= zsum (fun n => n) (rcl L) + zsum (fun n => n) (ekl L).

Lemma ekl_app L1 L2 : ekl (L1 ++ L2) = ekl L1 ++ ekl L2.
Proof. unfold ekl. rewrite map_app, concat_app. reflexivity. Qed.

Lemma rcl_app L1 L2 : rcl (L1 ++ L2) = rcl L1 ++ rcl L2.
Proof. unfold rcl. apply map_app. Qed.

Lemma chg_app u1 L1 u2 L2 : chg u1 L1 -> chg u2 L2 -> chg (u1 ++ u2) (L1 ++ L2).
Proof.
  intros [H1 B1] [H2 B2]. split.
  - intros c. rewrite ekl_app, rcl_app, !bcnt_app. specialize (H1 c). specialize (H2 c). lia.
  - rewrite ekl_app, rcl_app, !zsum_app. lia.
Qed.

Lemma chg_nil : chg [] [].
Proof. split; [intros c|]; cbn; lia. Qed.

Lemma last_space_spec l : forall i j, last_space_from i l = Some j ->
  (i <= j)%nat /\ (j - i < length l)%nat /\ nth (j - i) l 0 = SPACE.
Proof.
  induction l as [|b l IH]; intros i j H; [discriminate H|]. cbn [last_space_from] in H.
  destruct (last_space_from (S i) l) as [j0|] eqn:E.
  - injection H as <-. destruct (IH (S i) j0 E) as (H1 & H2 & H3). split; [lia|]. cbn [length].
    replace (j0 - i)%nat with (S (j0 - S i)) by lia. split; [lia|]. exact H3.
  - destruct (Z.eqb_spec b SPACE) as [Eb|Eb]; [|discriminate H]. injection H as <-.
    rewrite Nat.sub_diag. cbn [length nth]. split; [lia|]. split; [lia|]. exact Eb.
Qed.

Lemma firstn_S_nth (n : nat) (l : list Z) : (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  revert l. induction n as [|n IH]; intros [|x l] H; cbn [length] in H; try lia; [reflexivity|].
  cbn [firstn nth]. rewrite (IH l) by lia. reflexivity.
Qed.

Lemma skipn_nth_cons (n : nat) (l : list Z) : (n < length l)%nat -> skipn n l = nth n l 0 :: skipn (S n) l.
Proof.
  revert l. induction n as [|n IH]; intros [|x l] H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma list_eqb_eq a b : list_eqb a b = true -> a = b.
Proof. unfold list_eqb. destruct (list_eq_dec Z.eq_dec a b); [intros _; exact e|discriminate]. Qed.

Lemma zl_eqb_refl a : zl_eqb a a = true.
Proof. induction a as [|x a IH]; [reflexivity|]. cbn [zl_eqb]. rewrite Z.eqb_refl, IH. reflexivity. Qed.

Lemma gesture_begin l x : gesture l = Some (GBegin, x) -> Z.of_nat (length x) + 1 = zlen l - 5 /\ begin_line l = true.
Proof.
  unfold gesture. intros H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && (nth 13 l 0 =? SPACE) && (13 <? length l)%nat) eqn:E1;
    [|discriminate H].
  destruct (last_space_from 0 l) as [j|] eqn:E2; [|discriminate H].
  destruct (13 <? j)%nat eqn:E3; [|discriminate H].
  apply Nat.ltb_lt in E3.
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:E4.
  2: { destruct (list_eqb (skipn (S j) l) W_END); discriminate H. }
  injection H as <-. apply list_eqb_eq in E4.
  apply andb_true_iff in E1 as [E1 E5]. apply andb_true_iff in E1 as [E1 E6].
  apply list_eqb_eq in E1. apply Z.eqb_eq in E6. apply Nat.ltb_lt in E5.
  destruct (last_space_spec l 0 j E2) as (_ & Hj & Hsp). rewrite Nat.sub_0_r in Hj, Hsp.
  assert (Ls : length (skipn (S j) l) = 5%nat) by (rewrite E4; reflexivity).
  rewrite length_skipn in Ls.
  assert (Lx : length (firstn j l) = j) by (rewrite length_firstn; lia).
  unfold zlen. rewrite Lx. split; [lia|].
  unfold begin_line. apply andb_true_iff. split; [apply andb_true_iff; split|].
  - apply Z.leb_le. unfold zlen. lia.
  - rewrite (firstn_S_nth 13 l) by lia. rewrite E1, E6. apply zl_eqb_refl.
  - replace (length l - 6)%nat with j by lia. rewrite (skipn_nth_cons j l) by lia. rewrite Hsp, E4.
    apply zl_eqb_refl.
Qed.

Lemma LL_z : Z.of_nat LINE_LIMIT = 6000.
Proof. reflexivity. Qed.

Lemma LL_eq n : n = LINE_LIMIT -> Z.of_nat n = 6000.
Proof. intros ->. exact LL_z. Qed.

Lemma LL_ne n : n <> LINE_LIMIT -> Z.of_nat n <> 6000.
Proof. intros H E. apply H. apply Nat2Z.inj. rewrite E, LL_z. reflexivity. Qed.

Lemma LL_le n : (n <= LINE_LIMIT)%nat -> Z.of_nat n <= 6000.
Proof. intros H. apply Nat2Z.inj_le in H. rewrite LL_z in H. exact H. Qed.

Lemma ek1_line l : zlen l <= 6000 ->
  (forall c, bcnt c ((zlen l + 1) :: ek1 l ++ ek1 l) <= bcnt c (line_copies l)) /\
  zsum (fun n => n) ((zlen l + 1) :: ek1 l ++ ek1 l) <= zsum (fun n => n) (line_copies l) /\
  zsum (fun n => n) (ek1 l) <= zlen l + 1 /\ Forall (fun n => 0 <= n) (ek1 l).
Proof.
  intros HL.
  assert (E : line_copies l = (zlen l + 1) :: (if begin_line l then [zlen l - 5; zlen l - 5] else [])).
  { unfold line_copies. rewrite (proj2 (Z.leb_le (zlen l) LLIM)) by (unfold LLIM; lia). reflexivity. }
  rewrite E. unfold ek1.
  destruct (gesture l) as [[[|] x]|] eqn:Eg.
  - destruct (gesture_begin l x Eg) as [Ex Eb]. rewrite Eb, Ex. cbn [app].
    pose proof (begin_line_len l Eb). split; [intros c; lia|]. split; [lia|].
    split; [unfold zsum; cbn [fold_right]; lia|]. constructor; [lia|constructor].
  - cbn [app]. split; [intros c; rewrite !bcnt_cons; pose proof (bcnt_nonneg c (if begin_line l then [zlen l - 5; zlen l - 5] else [])); change (bcnt c []) with 0; lia|].
    split; [destruct (begin_line l) eqn:Eb; [pose proof (begin_line_len l Eb)|]; unfold zsum; cbn [fold_right]; lia|].
    split; [unfold zsum, zlen; cbn [fold_right]; lia|constructor].
  - cbn [app]. split; [intros c; rewrite !bcnt_cons; pose proof (bcnt_nonneg c (if begin_line l then [zlen l - 5; zlen l - 5] else [])); change (bcnt c []) with 0; lia|].
    split; [destruct (begin_line l) eqn:Eb; [pose proof (begin_line_len l Eb)|]; unfold zsum; cbn [fold_right]; lia|].
    split; [unfold zsum, zlen; cbn [fold_right]; lia|constructor].
Qed.

Lemma ekl_line L : Forall (fun l => zlen l <= 6000) L ->
  (forall c, bcnt c (ekl L) <= bcnt c (flat_map line_copies L)) /\
  zsum (fun n => n) (ekl L) <= zsum (fun n => n) (flat_map line_copies L) /\
  zsum (fun n => n) (ekl L) <= zsum (fun n => n) (rcl L) /\ Forall (fun n => 0 <= n) (ekl L).
Proof.
  induction L as [|l L IH]; intros HF; [cbn; split; [intros c; lia|]; split; [lia|]; split; [lia|constructor]|].
  apply Forall_cons_iff in HF as [Hl HF]. destruct (IH HF) as (I1 & I2 & I3 & I4).
  destruct (ek1_line l Hl) as (J1 & J2 & J3 & J4).
  change (ekl (l :: L)) with (ek1 l ++ ekl L). change (rcl (l :: L)) with ((zlen l + 1) :: rcl L).
  cbn [flat_map]. pose proof (zsum_id_nonneg _ J4) as N4.
  split; [intros c; specialize (J1 c); specialize (I1 c); rewrite bcnt_cons, bcnt_app in J1; rewrite !bcnt_app;
    pose proof (one_if_b c (band (zlen l + 1))); pose proof (bcnt_nonneg c (ek1 l)); lia|].
  rewrite zsum_cons, zsum_app in J2. cbv beta in J2. split; [rewrite !zsum_app; unfold zlen in *; lia|].
  split; [rewrite zsum_app, zsum_cons; cbv beta; lia|]. apply Forall_app. split; [exact J4|exact I4].
Qed.

Lemma chg_new L1 L2 : Forall (fun l => zlen l <= 6000) (L1 ++ L2) ->
  (forall c, bcnt c (rcl L1) + bcnt c (ekl L1) + bcnt c (ekl (L1 ++ L2)) <= bcnt c (flat_map line_copies (L1 ++ L2))) /\
  zsum (fun n => n) (rcl L1) + zsum (fun n => n) (ekl L1) + zsum (fun n => n) (ekl (L1 ++ L2)) <=
    zsum (fun n => n) (flat_map line_copies (L1 ++ L2)).
Proof.
  induction L1 as [|l L1 IH]; intros HF.
  - cbn [app]. destruct (ekl_line L2 HF) as (I1 & I2 & _).
    split; [intros c; specialize (I1 c); change (bcnt c (rcl [])) with 0; change (bcnt c (ekl [])) with 0; lia|].
    change (zsum (fun n => n) (rcl [])) with 0. change (zsum (fun n => n) (ekl [])) with 0. lia.
  - cbn [app] in HF |- *. apply Forall_cons_iff in HF as [Hl HF]. destruct (IH HF) as (I1 & I2).
    destruct (ek1_line l Hl) as (J1 & J2 & J3 & J4).
    change (ekl (l :: L1)) with (ek1 l ++ ekl L1). change (ekl (l :: L1 ++ L2)) with (ek1 l ++ ekl (L1 ++ L2)).
    change (rcl (l :: L1)) with ((zlen l + 1) :: rcl L1). cbn [flat_map].
    split.
    + intros c. specialize (J1 c). specialize (I1 c). rewrite bcnt_cons, bcnt_app in J1.
      rewrite bcnt_cons, !bcnt_app. lia.
    + rewrite zsum_cons, zsum_app in J2. cbv beta in J2. rewrite zsum_cons, !zsum_app. cbv beta. lia.
Qed.

Lemma lines_len6 d : forall st, (ls_k st = false -> zlen (ls_w st) <= 6000) ->
  Forall (fun l => zlen l <= 6000) (lines st d).
Proof.
  induction d as [|b d IH]; intros st H; [rewrite lines_nil; constructor|]. rewrite lines_cons.
  destruct (Z.eqb_spec b 0) as [->|Hb].
  - rewrite step_zero. cbn [fst snd]. destruct (ls_k st) eqn:Ek; cbv beta iota.
    + apply IH. intros _. unfold zlen. cbn. lia.
    + constructor; [exact (H eq_refl)|]. apply IH. intros _. unfold zlen. cbn. lia.
  - destruct (ls_k st) eqn:Ek.
    + rewrite (step_nz_k st b Hb Ek). cbn [fst snd]. apply IH. rewrite Ek. intros E. discriminate E.
    + destruct (Nat.eq_dec (length (ls_w st)) LINE_LIMIT) as [He|He].
      * rewrite (step_nz_full st b Hb Ek He). cbn [fst snd]. apply IH. cbn [ls_k]. intros E. discriminate E.
      * rewrite (step_nz_add st b Hb Ek He). cbn [fst snd]. apply IH. intros _. cbn [ls_w].
        unfold zlen. rewrite length_app. cbn [length]. specialize (H eq_refl). pose proof (LL_ne _ He).
        unfold zlen in H. lia.
Qed.

Lemma lines_count d : forall st, (length (lines st d) <= length d)%nat.
Proof.
  induction d as [|b d IH]; intros st; [rewrite lines_nil; cbn; lia|]. rewrite lines_cons. cbn [length].
  destruct (snd (step st b)); cbn [length]; specialize (IH (fst (step st b))); lia.
Qed.

Lemma lines_mass d : forall st,
  zsum (fun l => zlen l + 1) (lines st d) <= zlen d + (if ls_k st then 0 else zlen (ls_w st)).
Proof.
  unfold zlen. induction d as [|b d IH]; intros st.
  - rewrite lines_nil. cbn [zsum fold_right length]. destruct (ls_k st); cbv beta iota; lia.
  - rewrite lines_cons. cbn [length]. destruct (Z.eqb_spec b 0) as [->|Hb].
    + rewrite step_zero. cbn [fst snd]. specialize (IH (LS [] false)). cbn [ls_k ls_w length] in IH.
      destruct (ls_k st) eqn:Ek; cbv beta iota; [lia|]. rewrite zsum_cons. cbv beta. lia.
    + destruct (ls_k st) eqn:Ek; cbv beta iota.
      * rewrite (step_nz_k st b Hb Ek). cbn [fst snd]. specialize (IH st). rewrite Ek in IH. lia.
      * destruct (Nat.eq_dec (length (ls_w st)) LINE_LIMIT) as [He|He].
        -- rewrite (step_nz_full st b Hb Ek He). cbn [fst snd]. specialize (IH (LS (ls_w st) true)).
           cbn [ls_k] in IH. lia.
        -- rewrite (step_nz_add st b Hb Ek He). cbn [fst snd]. specialize (IH (LS (ls_w st ++ [b]) false)).
           cbn [ls_k ls_w] in IH. rewrite length_app in IH. cbn [length] in IH. lia.
Qed.

Definition lrel (st : lstate) (p : list Z) : Prop :=
  nozero p /\ (ls_k st = false -> p = ls_w st /\ zlen p <= 6000) /\ (ls_k st = true -> 6000 < zlen p).

Lemma zsegs_nz0 p d : nozero p -> zsegs (p ++ 0 :: d) = p :: zsegs d.
Proof.
  induction p as [|x p IH]; intros H; [reflexivity|]. inversion H as [|y q Hx Hp]; subst. cbn [app zsegs].
  rewrite (proj2 (Z.eqb_neq x 0) Hx), (IH Hp). reflexivity.
Qed.

Lemma line_copies_long p : 6000 < zlen p -> line_copies p = [].
Proof.
  intros H. unfold line_copies. rewrite (proj2 (Z.leb_gt (zlen p) LLIM)) by (unfold LLIM; lia). reflexivity.
Qed.

Lemma lines_segs d : forall st p, lrel st p ->
  flat_map line_copies (lines st d) = flat_map line_copies (removelast (zsegs (p ++ d))).
Proof.
  induction d as [|b d IH]; intros st p (Hz & Hf & Ht).
  - rewrite lines_nil, app_nil_r, (nozero_zsegs p Hz). reflexivity.
  - rewrite lines_cons. destruct (Z.eqb_spec b 0) as [->|Hb].
    + rewrite step_zero, (zsegs_nz0 p d Hz). cbn [fst snd].
      assert (IH0 : flat_map line_copies (lines (LS [] false) d) = flat_map line_copies (removelast (zsegs d))).
      { apply (IH (LS [] false) []). split; [constructor|]. cbn [ls_k ls_w]. split; [intros _; split; [reflexivity|unfold zlen; cbn; lia]|].
        intros E. discriminate E. }
      destruct (zsegs d) as [|s ss] eqn:Ez; [exfalso; exact (zsegs_ne d Ez)|].
      change (removelast (p :: s :: ss)) with (p :: removelast (s :: ss)).
      destruct (ls_k st) eqn:Ek.
      * cbn [flat_map]. rewrite IH0, (line_copies_long p (Ht eq_refl)). reflexivity.
      * destruct (Hf eq_refl) as [Ep _]. rewrite <- Ep. cbn [flat_map]. rewrite IH0. reflexivity.
    + replace (p ++ b :: d) with ((p ++ [b]) ++ d) by (rewrite <- app_assoc; reflexivity).
      assert (Hz' : nozero (p ++ [b])) by (apply Forall_app; split; [exact Hz|constructor; [exact Hb|constructor]]).
      destruct (ls_k st) eqn:Ek.
      * rewrite (step_nz_k st b Hb Ek). cbn [fst snd]. apply IH. split; [exact Hz'|].
        rewrite Ek. split; [intros E; discriminate E|]. intros _. specialize (Ht eq_refl). unfold zlen in *.
        rewrite length_app. cbn [length]. lia.
      * destruct (Hf eq_refl) as [Ep Hl].
        destruct (Nat.eq_dec (length (ls_w st)) LINE_LIMIT) as [He|He].
        -- rewrite (step_nz_full st b Hb Ek He). cbn [fst snd]. apply IH. split; [exact Hz'|].
           cbn [ls_k]. split; [intros E; discriminate E|]. intros _. unfold zlen. rewrite length_app, Ep.
           cbn [length]. pose proof (LL_eq _ He). lia.
        -- rewrite (step_nz_add st b Hb Ek He). cbn [fst snd]. apply IH. split; [exact Hz'|].
           cbn [ls_k ls_w]. split; [|intros E; discriminate E]. intros _. split; [rewrite Ep; reflexivity|].
           unfold zlen in *. rewrite length_app. cbn [length]. rewrite <- Ep in He. pose proof (LL_ne _ He). lia.
Qed.

Lemma tl_zsegs_skipn k : forall d, exists pre, tl (zsegs d) = pre ++ tl (zsegs (skipn k d)).
Proof.
  induction k as [|k IH]; intros d; [exists []; reflexivity|].
  destruct d as [|b d]; [exists []; reflexivity|]. cbn [skipn]. destruct (IH d) as (pre & E).
  cbn [zsegs]. destruct (zsegs d) as [|s ss] eqn:Ez; [exfalso; exact (zsegs_ne d Ez)|].
  cbn [tl] in E. destruct (b =? 0); cbn [tl].
  - exists (s :: pre). rewrite E. reflexivity.
  - exists pre. exact E.
Qed.

Lemma inner_skipn k d : exists pre, inner_segs d = pre ++ inner_segs (skipn k d).
Proof.
  unfold inner_segs. destruct (tl_zsegs_skipn k d) as (pre & E). rewrite E.
  destruct (tl (zsegs (skipn k d))) as [|s ss] eqn:Et.
  - exists (removelast pre). rewrite !app_nil_r. reflexivity.
  - exists pre. apply removelast_app. discriminate.
Qed.

Lemma skipn_map' {A B : Type} (f : A -> B) (n : nat) (l : list A) : skipn n (map f l) = map f (skipn n l).
Proof. revert l. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma bcnt_filter c xs : zlen (filter (fun q => band q =? c) xs) = bcnt c xs.
Proof.
  unfold zlen, bcnt. induction xs as [|x xs IH]; [reflexivity|]. cbn [filter]. rewrite zsum_cons. cbv beta.
  assert (E : one_if c (band x) = if band x =? c then 1 else 0) by (unfold one_if; rewrite Z.eqb_sym; reflexivity).
  rewrite E. destruct (band x =? c); cbn [length]; lia.
Qed.

Lemma rec_cred_skipn c k r : rec_cred c (skipn k r) <= rec_cred c r.
Proof.
  unfold rec_cred, plz. rewrite <- skipn_map'.
  destruct (inner_skipn k (map (fun b => bv_unsigned b) r)) as (pre & E). rewrite E, flat_map_app, filter_app.
  unfold zlen. rewrite length_app. lia.
Qed.

Lemma rec_credb_skipn k r : rec_credb (skipn k r) <= rec_credb r.
Proof.
  unfold rec_credb, plz. rewrite <- skipn_map'.
  destruct (inner_skipn k (map (fun b => bv_unsigned b) r)) as (pre & E). rewrite E, zsum_app.
  assert (0 <= zsum lmass pre) by (apply zsum_nonneg; intros l _; exact (proj1 (lc_mass_le l))). lia.
Qed.

Lemma new_cred h : (ls_k (hs_state h) = false -> zlen (ls_w (hs_state h)) <= 6000 /\ nozero (ls_w (hs_state h))) ->
  (forall c, bcnt c (flat_map line_copies (lines (hs_state h) (bzs (pending_stream h)))) <= cred h c) /\
  zsum (fun n => n) (flat_map line_copies (lines (hs_state h) (bzs (pending_stream h)))) <= credb h.
Proof.
  intros H.
  assert (P : exists p, lrel (hs_state h) p).
  { destruct (ls_k (hs_state h)) eqn:Ek.
    - exists (repeat 1 (Z.to_nat 6001)). split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
      split; [intros E; rewrite Ek in E; discriminate E|]. intros _. unfold zlen. rewrite repeat_length, Z2Nat.id by lia. lia.
    - exists (ls_w (hs_state h)). destruct (H eq_refl) as [H1 H2]. split; [exact H2|].
      split; [intros _; split; [reflexivity|exact H1]|]. intros E. rewrite Ek in E. discriminate E. }
  destruct P as (p & Hp). pose proof (proj1 Hp) as Hz.
  assert (ES : exists rs, bzs (pending_stream h) = concat (map plz rs) /\
            (forall c, zsum (rec_cred c) rs <= cred h c) /\ zsum rec_credb rs <= credb h).
  { unfold pending_stream, cred, credb. destruct (hl_recs (hs_pending h)) as [|r rs0].
    - exists []. cbn. split; [reflexivity|]. split; [intros c|]; lia.
    - exists (skipn (Z.to_nat (hs_off h)) (snd r) :: map snd rs0). split.
      + cbn [map concat]. unfold bzs. rewrite map_app, concat_map, !map_map. reflexivity.
      + cbn [map]. split; [intros c; rewrite !zsum_cons; pose proof (rec_cred_skipn c (Z.to_nat (hs_off h)) (snd r)); lia|].
        rewrite !zsum_cons. pose proof (rec_credb_skipn (Z.to_nat (hs_off h)) (snd r)). lia. }
  destruct ES as (rs & ES & C1 & C2).
  rewrite ES, (lines_segs _ _ p Hp). split.
  - intros c. rewrite <- bcnt_filter. eapply Z.le_trans; [apply (drain_cred rs p c Hz)|]. apply C1.
  - rewrite zsum_ffm. change (zsum (fun x => zsum (fun n => n) (line_copies x))) with (zsum lmass).
    eapply Z.le_trans; [apply (drain_credb rs p Hz)|]. exact C2.
Qed.
