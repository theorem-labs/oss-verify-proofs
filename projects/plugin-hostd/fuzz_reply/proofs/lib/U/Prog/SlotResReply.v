From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotEntryRun SlotPass0 SlotPass1w TrModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF ListTr HarnessRep RelayRep CheckRep HarnessTr relay_add_b_c op_add_c
  SlotMove SlotNcMove3 SlotRun3 SlotOp7R3 SlotResR3.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition exit_RV_s (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (dels adds : list (Z * Z)) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall G' out' es' hj',
    (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
    pend_view hj' = pend_view hj -> ek_view hj' = ek_view hj -> (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
    nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A' dels adds ->
    List.NoDup (map fst (blocks L' A')) ->
    (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
       In (ptr_addr L p) (rv_nc (view_of G out es hj)) -> ~ In (ptr_addr L p) (map fst dels) ->
       In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
    ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= nc_wt es hj ->
    RI E k (view_of G' out' es' hj') L' A'.

Definition reset_RV_s (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (h : hsrc) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall G' out' es' hj',
    (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
    (exists p1 p2, pend_view hj = p1 ++ map snd (hl_recs (hs_pending h)) :: p2 /\ pend_view hj' = p1 ++ p2) ->
    (exists e1 e2, ek_view hj = e1 ++ ekeys_hl (hs_expected h) ++ e2 /\ ek_view hj' = e1 ++ e2) ->
    (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
    nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A' (src_dels h) [] ->
    List.NoDup (map fst (blocks L' A')) ->
    (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
       In (ptr_addr L p) (rv_nc (view_of G out es hj)) -> ~ In (ptr_addr L p) (map fst (src_dels h)) ->
       In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
    ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= nc_wt es hj ->
    RI E k (view_of G' out' es' hj') L' A'.

Definition exit_res_reset_s (F : ResFormT) (RI : res_inv) (CS : list byte -> list Z) : Prop :=
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall k L A G out es hj, RI E k (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) ->
      res_tr F (exit_RV_s RI E k L A G out es hj [] []) A [] /\
      (forall mem HA h, src_at (rc := rc) B L A mem HA h ->
         res_tr F (reset_RV_s RI E k L A G out es hj h) A (source_reset_tr (known_at L A) h)).

Definition exit_res_ends_s (F : ResFormT) (RI : res_inv) (CS : list byte -> list Z) : Prop :=
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall k L A gone (rs : list (Z * list byte)) d G out es hj,
      RI E k (view_of G out es hj) L A -> (gone = 0 \/ gone = 1) ->
      Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A)) rs -> NoDup (map fst rs) ->
      res_tr F (exit_RV_s RI E k L A G out es hj [] []) A (check_shape_ends_tr (known_at L A) gone [] rs d).

Lemma prom_c_app P Q c : prom_c (P ++ Q) c = prom_c P c + prom_c Q c.
Proof. unfold prom_c. apply zsum_app. Qed.

Lemma promb_app P Q : promb (P ++ Q) = promb P + promb Q.
Proof. unfold promb. apply zsum_app. Qed.

Lemma prom_c_drop p1 X p2 c : prom_c (p1 ++ p2) c <= prom_c (p1 ++ X :: p2) c.
Proof.
  rewrite !prom_c_app.
  assert (E : prom_c (X :: p2) c = zsum (rec_cred c) X + prom_c p2 c) by (unfold prom_c; rewrite zsum_cons; reflexivity).
  assert (0 <= zsum (rec_cred c) X) by (apply zsum_nonneg; intros r _; pose proof (rec_cred_ge c r); lia).
  lia.
Qed.

Lemma promb_drop p1 X p2 : promb (p1 ++ p2) <= promb (p1 ++ X :: p2).
Proof.
  rewrite !promb_app.
  assert (E : promb (X :: p2) = zsum rec_credb X + promb p2) by (unfold promb; rewrite zsum_cons; reflexivity).
  assert (0 <= zsum rec_credb X)
    by (apply zsum_nonneg; intros r _; pose proof (rec_credb_ge r); unfold WILD_B, LLIM in *; lia).
  lia.
Qed.

Lemma ek_view_c G out es hj c : ek_c (view_of G out es hj) c = zsum (fun n => one_if c (band n)) (ek_view hj).
Proof. reflexivity. Qed.

Lemma ek_view_b G out es hj : ek_b (view_of G out es hj) = zsum (fun n => n) (ek_view hj).
Proof. reflexivity. Qed.

Lemma zsum_mid {X : Type} (f : X -> Z) l1 m l2 : 0 <= zsum f m -> zsum f (l1 ++ l2) <= zsum f (l1 ++ m ++ l2).
Proof. intros H. rewrite !zsum_app. lia. Qed.

Lemma cred_same E k G out es hj G' out' es' hj' : pend_view hj' = pend_view hj -> ek_view hj' = ek_view hj ->
  cred3 (ss_pl E) k k (view_of G out es hj) (view_of G' out' es' hj') [].
Proof.
  intros Hp Hek. split.
  - intros c Hc. rewrite !ek_view_c, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
    change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp. change (bcnt c []) with 0. lia.
  - rewrite !ek_view_b, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
    change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp, zsum_nil. lia.
Qed.

Lemma wt_view G out es hj : rv_wt (view_of G out es hj) = nc_wt es hj.
Proof. reflexivity. Qed.

Theorem exit_res_ends_reply_s : exit_res_ends_s pack3_form RI3_reply CS_reply.
Proof.
  intros B API LS SH SK ra empty rc fx j E HF k L A gone rs d G out es hj HRI Hg Hrs Hnd.
  destruct (ends_free (known_at L A) gone [] rs d) as (Hf & Hn1).
  assert (Hn : Forall (fun n => 0 <= n) (fsz (check_shape_ends_tr (known_at L A) gone [] rs d)))
    by (rewrite Forall_forall in *; intros n Hn; pose proof (Hn1 n Hn); lia).
  apply (res_tr_weaken _ _ _ _ _ (frees_res3 E k _ L A _ HRI Hf)).
  intros L' A' qs HP. hnf. intros G' out' es' hj' Hcov Hp Hek Hes Hhj HM HND HK HWs HWg.
  apply (HP (view_of G' out' es' hj') [] Hn).
  - intros c Hc. rewrite zsum_nil. apply bcnt_nonneg.
  - rewrite zsum_nil. exact (zsum_id_nonneg _ Hn).
  - intros p n _ [].
  - exact HM.
  - exact HND.
  - exact HK.
  - exact (nc_len G' out' es' hj' Hes Hhj).
  - exact HWs.
  - rewrite !wt_view. exact HWg.
  - exact (cred_same E k G out es hj G' out' es' hj' Hp Hek).
  - exact (ek_view_nonneg hj').
Qed.

Theorem exit_res_reset_reply_s : exit_res_reset_s pack3_form RI3_reply CS_reply.
Proof.
  intros B API LS SH SK ra empty rc fx j E HF k L A G out es hj HRI HND0. split.
  - apply (res_tr_weaken _ _ _ _ _ (frees_res3 E k _ L A [] HRI (Forall_nil _))).
    intros L' A' qs HP. hnf. intros G' out' es' hj' Hcov Hp Hek Hes Hhj HM HND HK HWs HWg.
    apply (HP (view_of G' out' es' hj') [] (Forall_nil _)).
    + intros c Hc. rewrite zsum_nil. apply bcnt_nonneg.
    + change (fsz []) with (@nil Z). rewrite !zsum_nil. lia.
    + intros p n _ [].
    + exact HM.
    + exact HND.
    + exact HK.
    + exact (nc_len G' out' es' hj' Hes Hhj).
    + exact HWs.
    + rewrite !wt_view. exact HWg.
    + exact (cred_same E k G out es hj G' out' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
  - intros mem HA h Hsrc.
    apply (res_tr_weaken _ _ _ _ _ (frees_res3 E k _ L A _ HRI (reset_free (known_at L A) h))).
    intros L' A' qs HP. hnf.
    intros G' out' es' hj' Hcov (p1 & p2 & Hp & Hp') (e1 & e2 & He & He') Hes Hhj HM HND HK HWs HWg.
    pose proof HM as (R & gone & B0 & X & Y & _ & _ & _ & _ & _ & Hdel & _).
    apply (HP (view_of G' out' es' hj') (src_dels h) (reset_nonneg (known_at L A) h Hdel)).
    + intros c Hc. exact (reset_sum (fun n => one_if c (band n)) (known_at L A) h (fun x _ => proj1 (one_if_b c (band x)))).
    + exact (reset_sum (fun n => n) (known_at L A) h (fun x Hx => Z.le_trans _ _ _ Z.le_0_1 Hx)).
    + intros p n Hpn Hx. rewrite <- (sptr_of_at L A p n HND0 Hpn). exact (reset_free_at (known_at L A) h _ Hx).
    + exact HM.
    + exact HND.
    + exact HK.
    + exact (nc_len G' out' es' hj' Hes Hhj).
    + exact HWs.
    + rewrite !wt_view. exact HWg.
    + pose proof (ek_view_nonneg hj) as EN. rewrite He in EN. apply Forall_app in EN as [_ EN].
      apply Forall_app in EN as [EN _].
      assert (EB : 0 <= zsum (fun n => n) (ekeys_hl (hs_expected h))) by (apply zsum_id_nonneg; exact EN).
      assert (EC : forall c, 0 <= zsum (fun n => one_if c (band n)) (ekeys_hl (hs_expected h)))
        by (intros c; apply zsum_nonneg; intros n _; exact (proj1 (one_if_b c (band n)))).
      split.
      * intros c Hc. rewrite !ek_view_c, He, He'. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
        change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp, Hp'.
        pose proof (prom_c_drop p1 (map snd (hl_recs (hs_pending h))) p2 c).
        pose proof (zsum_mid (fun n => one_if c (band n)) e1 (ekeys_hl (hs_expected h)) e2 (EC c)).
        change (bcnt c []) with 0. lia.
      * rewrite !ek_view_b, He, He'. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
        change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp, Hp'.
        pose proof (promb_drop p1 (map snd (hl_recs (hs_pending h))) p2).
        pose proof (zsum_mid (fun n => n) e1 (ekeys_hl (hs_expected h)) e2 EB). rewrite zsum_nil. lia.
    + exact (ek_view_nonneg hj').
Qed.

Lemma zlen_as_zsum {X : Type} (l : list X) : zlen l = zsum (fun _ => 1) l.
Proof. induction l as [|x l IH]; [reflexivity|]. rewrite zsum_cons. unfold zlen in *. cbn [length]. lia. Qed.

Lemma zsum_filter_plus {X : Type} (w : X -> Z) (p q : X -> bool) l x :
  (forall y, p y = true -> q y = true) -> (forall y, 0 <= w y) -> In x l -> p x = false -> q x = true ->
  zsum w (filter p l) + w x <= zsum w (filter q l).
Proof.
  intros Hpq Hw Hin Hpx Hqx. induction l as [|y l IH]; [destruct Hin|].
  pose proof (zsum_filter_mono w p q l Hpq Hw) as M.
  cbn [filter]. destruct Hin as [Ey|Hin].
  - subst y. rewrite Hpx, Hqx. cbv beta iota. rewrite zsum_cons. lia.
  - specialize (IH Hin). destruct (p y) eqn:Ep.
    + rewrite (Hpq y Ep). cbv beta iota. rewrite !zsum_cons. lia.
    + destruct (q y); cbv beta iota; [rewrite zsum_cons; pose proof (Hw y); lia|exact IH].
Qed.

Lemma prom_c_push p1 x p2 txt c : prom_c (p1 ++ (x ++ [txt]) :: p2) c = prom_c (p1 ++ x :: p2) c + rec_cred c txt.
Proof. unfold prom_c. rewrite !zsum_app, !zsum_cons. cbv beta. rewrite zsum_app, zsum_cons, zsum_nil. lia. Qed.

Lemma promb_push p1 x p2 txt : promb (p1 ++ (x ++ [txt]) :: p2) = promb (p1 ++ x :: p2) + rec_credb txt.
Proof. unfold promb. rewrite !zsum_app, !zsum_cons. cbv beta. rewrite zsum_app, zsum_cons, zsum_nil. lia. Qed.

Definition ckw_c (c : Z) (x : ck) : Z := zlen (filter (fun r => band r =? c) (ck_copies x)).

Lemma cons_chunk pl k k' ch c : In ch (pl_chunks pl) -> ck_op ch = 1 -> k < ck_end ch <= k' ->
  cons_c pl k c + ckw_c c ch + 3 <= cons_c pl k' c.
Proof.
  intros Hin Hop He. unfold cons_c, xcount, ckw_c. rewrite !zlen_ffm.
  assert (D : forall x, done_ck k x = true -> done_ck k' x = true).
  { intros x. unfold done_ck. intros H. apply Z.leb_le in H. apply Z.leb_le. lia. }
  assert (Pk : done_ck k ch = false) by (unfold done_ck; apply Z.leb_gt; lia).
  assert (Pk' : done_ck k' ch = true) by (unfold done_ck; apply Z.leb_le; lia).
  pose proof (zsum_filter_plus (fun x => zlen (filter (fun r => band r =? c) (ck_copies x))) (done_ck k) (done_ck k')
    (pl_chunks pl) ch D (fun y => ltac:(cbv beta; unfold zlen; lia)) Hin Pk Pk') as X1.
  assert (D1 : forall x, done1 k x = true -> done1 k' x = true).
  { intros x Hx. unfold done1 in *. apply andb_prop in Hx as [Hx1 Hx2]. rewrite (D x Hx1), Hx2. reflexivity. }
  assert (P1 : done1 k ch = false) by (unfold done1; rewrite Pk; reflexivity).
  assert (P1' : done1 k' ch = true) by (unfold done1; rewrite Pk', Hop; reflexivity).
  pose proof (zsum_filter_plus (fun _ => 1) (done1 k) (done1 k') (pl_chunks pl) ch D1 (fun _ => Z.le_0_1) Hin P1 P1')
    as X2.
  rewrite (zlen_as_zsum (filter (done1 k) (pl_chunks pl))), (zlen_as_zsum (filter (done1 k') (pl_chunks pl))).
  cbv beta in X1, X2 |- *. lia.
Qed.

Lemma consb_chunk pl k k' ch : In ch (pl_chunks pl) -> ck_op ch = 1 -> k < ck_end ch <= k' ->
  consb pl k + cmass ch + WILD_B <= consb pl k'.
Proof.
  intros Hin Hop He. unfold consb.
  assert (D : forall x, done_ck k x = true -> done_ck k' x = true).
  { intros x. unfold done_ck. intros H. apply Z.leb_le in H. apply Z.leb_le. lia. }
  assert (Pk : done_ck k ch = false) by (unfold done_ck; apply Z.leb_gt; lia).
  assert (Pk' : done_ck k' ch = true) by (unfold done_ck; apply Z.leb_le; lia).
  pose proof (zsum_filter_plus cmass (done_ck k) (done_ck k') (pl_chunks pl) ch D cmass_nonneg Hin Pk Pk') as X1.
  assert (D1 : forall x, done1 k x = true -> done1 k' x = true).
  { intros x Hx. unfold done1 in *. apply andb_prop in Hx as [Hx1 Hx2]. rewrite (D x Hx1), Hx2. reflexivity. }
  assert (P1 : done1 k ch = false) by (unfold done1; rewrite Pk; reflexivity).
  assert (P1' : done1 k' ch = true) by (unfold done1; rewrite Pk', Hop; reflexivity).
  pose proof (zsum_filter_plus (fun _ => 1) (done1 k) (done1 k') (pl_chunks pl) ch D1 (fun _ => Z.le_0_1) Hin P1 P1')
    as X2.
  rewrite (zlen_as_zsum (filter (done1 k) (pl_chunks pl))), (zlen_as_zsum (filter (done1 k') (pl_chunks pl))).
  cbv beta in X2. unfold WILD_B, LLIM. lia.
Qed.

Lemma cdat_chunk pl k k' ch : In ch (pl_chunks pl) -> ck_op ch = 1 -> k < ck_end ch <= k' ->
  cdat pl k + zlen (ck_data ch) <= cdat pl k'.
Proof.
  intros Hin Hop He. unfold cdat.
  assert (D1 : forall x, done1 k x = true -> done1 k' x = true).
  { intros x Hx. unfold done1, done_ck in *. apply andb_prop in Hx as [Hx1 Hx2]. apply Z.leb_le in Hx1.
    rewrite Hx2, andb_true_r. apply Z.leb_le. lia. }
  assert (Pk : (ck_end ch <=? k) = false) by (apply Z.leb_gt; lia).
  assert (Pk' : (ck_end ch <=? k') = true) by (apply Z.leb_le; lia).
  assert (P1 : done1 k ch = false) by (unfold done1, done_ck; rewrite Pk; reflexivity).
  assert (P1' : done1 k' ch = true) by (unfold done1, done_ck; rewrite Pk', Hop; reflexivity).
  exact (zsum_filter_plus (fun x => zlen (ck_data x)) (done1 k) (done1 k') (pl_chunks pl) ch D1
    (fun y => ltac:(unfold zlen; lia)) Hin P1 P1').
Qed.

Lemma ckw_push c a txt : ckw_c c (CK 1 a (plz txt)) = one_if c (band (zlen (plz txt) + 1)) + rec_cred c txt - 3.
Proof.
  unfold ckw_c, rec_cred, ck_copies. cbn [ck_op ck_data]. change (1 =? 7) with false. cbv iota.
  cbn [filter]. unfold one_if.
  destruct (Z.eqb_spec (band (zlen (plz txt) + 1)) c) as [E1|E1];
    destruct (Z.eqb_spec c (band (zlen (plz txt) + 1))) as [E2|E2]; try lia; cbv iota; unfold zlen; cbn [length];
    lia.
Qed.

Lemma cmass_push a txt : cmass (CK 1 a (plz txt)) = zlen (plz txt) + 1 + rec_credb txt - WILD_B.
Proof.
  unfold cmass, rec_credb, ck_copies. cbn [ck_op ck_data]. change (1 =? 7) with false. cbv iota.
  rewrite zsum_cons, zsum_ffm. cbv beta. unfold lmass. lia.
Qed.

Lemma pend_len hj : pend_view hj = [[]] -> (length hj <= 4)%nat.
Proof. intros H. assert (E : length (pend_view hj) = length hj) by apply length_map. rewrite H in E. cbn in E. lia. Qed.

Lemma push_link L' qs nm l x l' : hl_n l = hl_cap l -> sh_real L' qs (list_push_sh 0 (sh_of nm l) x) l' ->
  ptr_addr L' (resolveF qs (Ret 0)) = hl_v l'.
Proof.
  intros E (_ & Hv & _). unfold list_push_sh in Hv.
  assert (En : sh_n (sh_of nm l) = hl_n l) by (unfold sh_n, sh_of, hl_n; cbn [sh_recs]; rewrite length_map; reflexivity).
  change (sh_cap (sh_of nm l)) with (hl_cap l) in Hv. rewrite En, E, Z.eqb_refl in Hv. cbn [sh_cap sh_v] in Hv.
  symmetry. apply Hv. unfold grow_cap. rewrite Z.eqb_refl. destruct (Z.eqb_spec (hl_cap l) 0); lia.
Qed.

Theorem entry_res_reply_s : entry_add_resources_s pack3_form RI3_reply.
Proof.
  intros E L A C G OUT HRI HC.
  assert (CR : forall G' OUT' es' hj', pend_view hj' = [[]] -> ek_view hj' = [] ->
      cred3 (ss_pl E) 0 0 (RV [] [G; OUT] NC_FIX []) (view_of G' OUT' es' hj') []).
  { intros G' OUT' es' hj' Hp Hek. split.
    - intros c Hc. rewrite ek_view_c, Hek. change (rv_pend (view_of G' OUT' es' hj')) with (pend_view hj'). rewrite Hp.
      change (bcnt c []) with 0. change (prom_c [[]] c) with 0. change (ek_c (RV [] [G; OUT] NC_FIX []) c) with 0.
      change (prom_c (rv_pend (RV [] [G; OUT] NC_FIX [])) c) with 0. rewrite zsum_nil. lia.
    - rewrite ek_view_b, Hek. change (rv_pend (view_of G' OUT' es' hj')) with (pend_view hj'). rewrite Hp.
      change (promb [[]]) with 0. change (ek_b (RV [] [G; OUT] NC_FIX [])) with 0.
      change (promb (rv_pend (RV [] [G; OUT] NC_FIX []))) with 0. rewrite !zsum_nil. lia. }
  destruct HC as [-> | ->].
  - change (op_add_tr (Some 0%nat) FIRST_FD 0 0 (known_at L A G)) with (map (@RMalloc sptr) [PARTIAL_BYTES; SRC_TABLE]).
    apply (res_tr_weaken _ _ _ _ _ (mallocs_res3 E 0 0 _ L A [PARTIAL_BYTES; SRC_TABLE] HRI
      ltac:(repeat constructor; unfold PARTIAL_BYTES, SRC_TABLE, SRC_ENTRY, NMAX; lia) ltac:(cbn; lia))).
    intros L' A' qs HP q g _ _ G' OUT' es' hj' Hcov Hp Hek Hes HM HND HK HWs HWg.
    apply (HP (view_of G' OUT' es' hj') (entry_adds q g 0) eq_refl HM HND HK
      (nc_len G' OUT' es' hj' Hes (pend_len hj' Hp)) HWs).
    + change (rv_wt (view_of G' OUT' es' hj')) with (nc_wt es' hj'). change (rv_wt (RV [] [G; OUT] NC_FIX [])) with NC_FIX.
      lia.
    + exact (CR G' OUT' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
  - change (op_add_tr (Some 0%nat) FIRST_FD 0 16 (known_at L A G)) with (map (@RMalloc sptr) [PARTIAL_BYTES]).
    apply (res_tr_weaken _ _ _ _ _ (mallocs_res3 E 0 0 _ L A [PARTIAL_BYTES] HRI
      ltac:(repeat constructor; unfold PARTIAL_BYTES, NMAX; lia) ltac:(cbn; lia))).
    intros L' A' qs HP q g _ _ G' OUT' es' hj' Hcov Hp Hek Hes HM HND HK HWs HWg.
    apply (HP (view_of G' OUT' es' hj') (entry_adds q g 16) eq_refl HM HND HK
      (nc_len G' OUT' es' hj' Hes (pend_len hj' Hp)) HWs).
    + change (rv_wt (view_of G' OUT' es' hj')) with (nc_wt es' hj'). change (rv_wt (RV [] [G; OUT] NC_FIX [])) with NC_FIX.
      lia.
    + exact (CR G' OUT' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
Qed.

Theorem op0_res_reply_s : op0_res_s RI3_reply.
Proof.
  intros E k L A i FD N G out es hj HRI Hk Hop HN.
  assert (CR : forall G' out' es' hj', pend_view hj' = pend_view hj ++ op0_pend i -> ek_view hj' = ek_view hj ->
      cred3 (ss_pl E) k k (view_of G out es hj) (view_of G' out' es' hj') []).
  { intros G' out' es' hj' Hp Hek.
    assert (Z0 : forall c, prom_c (op0_pend i) c = 0) by (intros c; destruct i; reflexivity).
    assert (Z1 : promb (op0_pend i) = 0) by (destruct i; reflexivity).
    split.
    - intros c Hc. rewrite !ek_view_c, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp, prom_c_app, Z0.
      change (bcnt c []) with 0. lia.
    - rewrite !ek_view_b, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp, promb_app, Z1, zsum_nil. lia. }
  rewrite (op0_tr i FD N (known_at L A G) HN). destruct i as [i0|].
  - change [RMalloc PARTIAL_BYTES] with (map (@RMalloc sptr) [PARTIAL_BYTES]).
    apply (res_tr_weaken _ _ _ _ _ (mallocs_res3 E k k _ L A [PARTIAL_BYTES] HRI
      ltac:(repeat constructor; unfold PARTIAL_BYTES, NMAX; lia) ltac:(cbn; lia))).
    intros L' A' qs HP q _. hnf. intros G' out' es' hj' Hcov Hp Hek Hes Hhj HM HND HK HWs HWg.
    apply (HP (view_of G' out' es' hj') (op0_adds q (Some i0)) eq_refl HM HND HK (nc_len G' out' es' hj' Hes Hhj) HWs).
    + change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj'). change (rv_wt (view_of G out es hj)) with (nc_wt es hj).
      lia.
    + exact (CR G' out' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
  - apply (res_tr_weaken _ _ _ _ _ (mallocs_res3 E k k _ L A [] HRI (Forall_nil _) ltac:(cbn; lia))).
    intros L' A' qs HP q _. hnf. intros G' out' es' hj' Hcov Hp Hek Hes Hhj HM HND HK HWs HWg.
    apply (HP (view_of G' out' es' hj') (op0_adds q None) eq_refl HM HND HK (nc_len G' out' es' hj' Hes Hhj) HWs).
    + change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj'). change (rv_wt (view_of G out es hj)) with (nc_wt es hj).
      lia.
    + exact (CR G' out' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
Qed.

Theorem push_res_reply_s : push_resources_s pack3_form RI3_reply.
Proof.
  intros E k k' L A l tx G out es hj HRI HND0 HN HNo HC Hn Hk' Hkn.
  assert (Hlx : length (bzs tx) = length tx) by (unfold bzs; apply length_map).
  pose proof (push_res3 E k k' (view_of G out es hj) L A l (bzs tx) HRI HND0 HN HC
    ltac:(rewrite Hlx; exact Hn)) as R.
  rewrite Hlx in R. apply (res_tr_weaken _ _ _ _ _ R).
  intros L' A' qs HP. hnf.
  intros l' Hreal _ G' out' es' hj' Hcov (p1 & xx & p2 & txt & Hp & Hp' & Hxx & Ht & Hin) Hek Hes Hhj HM HND HK
    HWs HWg.
  assert (Hz : zlen (plz txt) = Z.of_nat (length tx)) by (unfold zlen, plz; rewrite length_map; exact Ht).
  assert (Hend : k < ck_end (CK 1 (k' - Z.of_nat (length tx)) (plz txt)) <= k')
    by (unfold ck_end; cbn [ck_at ck_data]; lia).
  apply (HP (view_of G' out' es' hj') (hl_v l') (fun EN => push_link L' qs (known_at L A) l (bzs tx) l' EN Hreal)
    HM HND HK (nc_len G' out' es' hj' Hes Hhj) HWs).
  - change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj'). change (rv_wt (view_of G out es hj)) with (nc_wt es hj).
    pose proof (cdat_chunk (ss_pl E) k k' _ Hin eq_refl Hend) as CD. cbn [ck_data] in CD. rewrite Hz in CD.
    change (zlen [Z.of_nat (length tx) + 1]) with 1. unfold NC_PER, DATA_PER in *. lia.
  - split.
    + intros c Hc. rewrite !ek_view_c, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp', prom_c_push, <- Hp.
      pose proof (cons_chunk (ss_pl E) k k' _ c Hin eq_refl Hend) as C1. rewrite ckw_push, Hz in C1.
      rewrite bcnt_cons. change (bcnt c []) with 0. lia.
    + rewrite !ek_view_b, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp', promb_push, <- Hp.
      pose proof (consb_chunk (ss_pl E) k k' _ Hin eq_refl Hend) as C2. rewrite cmass_push, Hz in C2.
      rewrite zsum_cons, zsum_nil. lia.
  - exact (ek_view_nonneg hj').
Qed.
