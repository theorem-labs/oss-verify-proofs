From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF ListTr HarnessRep RelayRep CheckRep HarnessTr relay_add_b_c op_add_c
  SlotMove SlotNcMove3 SlotRun3 SlotOp7R3.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition dl_of (dels adds : list (Z * Z)) (c : Z) : Z :=
  zsum (fun t => one_if c (band (snd t))) adds - zsum (fun t => one_if c (band (snd t))) dels.

Definition db_of (dels adds : list (Z * Z)) : Z := zsum snd adds - zsum snd dels.

Lemma r3_sz_ind l q : nm3_sz l q = zsum (fun t => if fst t =? q then snd t else 0) l.
Proof.
  induction l as [|[a m] l IH]; [reflexivity|]. rewrite nm3_sz_cons, zsum_cons, IH. cbn [fst snd]. reflexivity.
Qed.

Lemma r3_sz_perm l l' q : Permutation l l' -> nm3_sz l q = nm3_sz l' q.
Proof. intros H. rewrite !r3_sz_ind. apply nm3_perm. exact H. Qed.

Lemma r3_sz_nonneg l q : (forall t, In t l -> 0 <= snd t) -> 0 <= nm3_sz l q.
Proof.
  intros H. rewrite r3_sz_ind. apply zsum_nonneg. intros t Ht. cbv beta. pose proof (H t Ht).
  destruct (fst t =? q); cbv iota; lia.
Qed.

Lemma r3_sz_ge l t : In t l -> (forall u, In u l -> 0 <= snd u) -> snd t <= nm3_sz l (fst t).
Proof.
  induction l as [|[a m] l IH]; intros Hin H; [destruct Hin|]. rewrite nm3_sz_cons.
  pose proof (r3_sz_nonneg l (fst t) (fun v Hv => H v (or_intror Hv))). destruct Hin as [<-|Hin].
  - cbn [fst snd] in *. rewrite Z.eqb_refl. cbv iota. lia.
  - pose proof (IH Hin (fun v Hv => H v (or_intror Hv))). pose proof (H (a, m) (or_introl eq_refl)). cbn [snd] in *.
    destruct (a =? fst t); cbv iota; lia.
Qed.

Lemma r3_sz_at l t : List.NoDup (map fst l) -> In t l -> nm3_sz l (fst t) = snd t.
Proof.
  induction l as [|[a m] l IH]; intros HN Ht; [destruct Ht|]. cbn [map fst] in HN.
  apply List.NoDup_cons_iff in HN as [Ha HN]. rewrite nm3_sz_cons. destruct Ht as [<-|Ht].
  - cbn [fst snd]. rewrite Z.eqb_refl, (nm3_sz_none l a Ha). cbv iota. lia.
  - destruct (Z.eqb_spec a (fst t)) as [E|E].
    + exfalso. apply Ha. rewrite E. apply in_map. exact Ht.
    + cbv iota. rewrite (IH HN Ht). lia.
Qed.

Lemma r3_has_true L A c q : nc_has L A c q = true <-> exists m, In (q, m) (blocks L A) /\ band m = c.
Proof.
  unfold nc_has. rewrite existsb_exists. split.
  - intros ([p m] & Hin & H). apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1, H2. cbn [fst snd] in *.
    subst. exists m. split; [exact Hin|reflexivity].
  - intros (m & Hin & Hb). exists (q, m). split; [exact Hin|]. cbn [fst snd]. rewrite Z.eqb_refl, Hb, Z.eqb_refl.
    reflexivity.
Qed.

Lemma r3_fst_eq (l : list (Z * Z)) t u : List.NoDup (map fst l) -> In t l -> In u l -> fst t = fst u -> t = u.
Proof.
  induction l as [|v l IH]; intros HN Ht Hu He; [destruct Ht|].
  cbn [map] in HN. apply List.NoDup_cons_iff in HN as [Hv HN].
  destruct Ht as [Et|Ht], Hu as [Eu|Hu].
  - congruence.
  - subst t. exfalso. apply Hv. rewrite He. apply in_map. exact Hu.
  - subst u. exfalso. apply Hv. rewrite <- He. apply in_map. exact Ht.
  - apply IH; assumption.
Qed.

Lemma one_if_eq c : one_if c c = 1.
Proof. unfold one_if. rewrite Z.eqb_refl. reflexivity. Qed.

Theorem nc_move_grow3 V L A V' L' A' dels adds : nc_move V L A V' L' A' dels adds ->
  (forall c, 0 <= c < 49 -> nc_cnt V L A c + dl_of dels adds c <= nc_cnt V' L' A' c) /\
  ncs V L A + db_of dels adds <= ncs V' L' A'.
Proof.
  intros (R & gone & B & X & Y & HV & HV' & HB & HB' & Hpos & Hdel & HdN & HdR & HY & Hg).
  assert (InB' : forall t, In t (B ++ adds ++ X) -> In t (blocks L' A')).
  { intros t Ht. exact (Permutation_in _ (Permutation_sym HB') Ht). }
  assert (Pos : forall t, In t (B ++ adds ++ X) -> 0 <= snd t).
  { intros [q m] Ht. exact (Hpos q m (InB' _ Ht)). }
  assert (PosA : forall t, In t adds -> 0 <= snd t).
  { intros t Ht. apply Pos. apply in_or_app. right. apply in_or_app. left. exact Ht. }
  assert (PosX : forall t, In t X -> 0 <= snd t).
  { intros t Ht. apply Pos. apply in_or_app. right. apply in_or_app. right. exact Ht. }
  assert (PosB' : forall t, In t (blocks L' A') -> 0 <= snd t) by (intros [q m] Ht; exact (Hpos q m Ht)).
  split.
  - intros c Hc. unfold dl_of. rewrite !nm3_cnt, (nm3_perm _ _ _ HV), (nm3_perm _ _ _ HV'), !zsum_app, !zsum_map.
    assert (S1 : zsum (fun q => if nc_has L A c q then 1 else 0) R <=
                 zsum (fun q => if nc_has L' A' c q then 1 else 0) R).
    { apply zsum_le'. intros p Hp. cbv beta. destruct (nc_has L A c p) eqn:E; cbv iota.
      - apply r3_has_true in E as (m & Hm & Hb).
        assert (E' : nc_has L' A' c p = true).
        { apply r3_has_true. exists m. split; [|exact Hb]. apply InB'. apply in_or_app. left.
          apply (Permutation_in _ HB) in Hm. apply in_app_or in Hm as [Hm|Hm]; [exact Hm|].
          exfalso. apply in_app_or in Hm as [Hm|Hm]; [exact (proj1 (HdR _ Hm) Hp)|exact (proj1 (HY _ Hm) Hp)]. }
        rewrite E'. cbv iota. lia.
      - destruct (nc_has L' A' c p); cbv iota; lia. }
    assert (S2 : zsum (fun t => if nc_has L A c (fst t) then 1 else 0) dels <=
                 zsum (fun t => one_if c (band (snd t))) dels).
    { apply zsum_le'. intros t Ht. cbv beta. pose proof (one_if_b c (band (snd t))).
      destruct (nc_has L A c (fst t)) eqn:E; cbv iota; [|lia].
      apply r3_has_true in E as (m & Hm & Hb). apply (Permutation_in _ HB) in Hm.
      apply in_app_or in Hm as [Hm|Hm]; [exfalso; exact (proj2 (HdR _ Ht) m Hm)|].
      apply in_app_or in Hm as [Hm|Hm]; [|exfalso; exact (proj2 (HY _ Hm) (in_map fst dels t Ht))].
      assert (Et : (fst t, m) = t) by (apply (r3_fst_eq dels); [exact HdN|exact Hm|exact Ht|reflexivity]).
      replace (snd t) with m by (rewrite <- Et; reflexivity). rewrite Hb, one_if_eq. lia. }
    assert (S3 : zsum (fun q => if nc_has L A c q then 1 else 0) gone <= 0).
    { assert (zsum (fun q => if nc_has L A c q then 1 else 0) gone <= 0 * Z.of_nat (length gone)); [|lia].
      apply zsum_le_bound. intros g Hg'. cbv beta. destruct (nc_has L A c g) eqn:E; cbv iota; [|lia].
      apply r3_has_true in E as (m & Hm & _). exfalso. exact (Hg g Hg' m Hm). }
    assert (S4 : zsum (fun t => one_if c (band (snd t))) adds <=
                 zsum (fun t => if nc_has L' A' c (fst t) then 1 else 0) adds).
    { apply zsum_le'. intros t Ht. cbv beta. unfold one_if.
      destruct (Z.eqb_spec c (band (snd t))) as [E|E]; cbv iota.
      - assert (E' : nc_has L' A' c (fst t) = true).
        { apply r3_has_true. exists (snd t). split; [|symmetry; exact E]. apply InB'. apply in_or_app. right.
          apply in_or_app. left. destruct t as [q m]. exact Ht. }
        rewrite E'. cbv iota. lia.
      - destruct (nc_has L' A' c (fst t)); cbv iota; lia. }
    cbv beta. lia.
  - unfold ncs, db_of. rewrite (nm3_perm _ _ _ HV), (nm3_perm _ _ _ HV'), !zsum_app, !zsum_map.
    assert (T1 : zsum (nc_sz L A) R <= zsum (nc_sz L' A') R).
    { apply zsum_le'. intros p Hp. rewrite !nm3_sz_b, (r3_sz_perm _ _ _ HB), (r3_sz_perm _ _ _ HB'), !nm3_sz_app.
      rewrite (nm3_sz_none dels p).
      2: { intros Hm. apply in_map_iff in Hm as (t & Et & Ht). subst p. exact (proj1 (HdR _ Ht) Hp). }
      rewrite (nm3_sz_none Y p).
      2: { intros Hm. apply in_map_iff in Hm as (t & Et & Ht). subst p. exact (proj1 (HY _ Ht) Hp). }
      pose proof (r3_sz_nonneg adds p PosA). pose proof (r3_sz_nonneg X p PosX). lia. }
    assert (T2 : zsum (fun t => nc_sz L A (fst t)) dels <= zsum snd dels).
    { apply zsum_le'. intros t Ht. cbv beta. rewrite nm3_sz_b, (r3_sz_perm _ _ _ HB), !nm3_sz_app, (r3_sz_at dels t HdN Ht).
      rewrite (nm3_sz_none B (fst t)).
      2: { intros Hm. apply in_map_iff in Hm as ([a m] & Ea & Hm). cbn [fst] in Ea. subst a.
           exact (proj2 (HdR _ Ht) m Hm). }
      rewrite (nm3_sz_none Y (fst t)).
      2: { intros Hm. apply in_map_iff in Hm as (u & Eu & Hu). apply (proj2 (HY _ Hu)). rewrite Eu.
           apply in_map. exact Ht. }
      lia. }
    assert (T3 : zsum (nc_sz L A) gone <= 0).
    { assert (zsum (nc_sz L A) gone <= 0 * Z.of_nat (length gone)); [|lia].
      apply zsum_le_bound. intros g Hg'. rewrite nm3_sz_b, nm3_sz_none; [lia|].
      intros Hm. apply in_map_iff in Hm as ([a m] & Ea & Hm). cbn [fst] in Ea. subst a. exact (Hg g Hg' m Hm). }
    assert (T4 : zsum snd adds <= zsum (fun t => nc_sz L' A' (fst t)) adds).
    { apply zsum_le'. intros t Ht. cbv beta. rewrite nm3_sz_b. apply r3_sz_ge; [|exact PosB'].
      apply InB'. apply in_or_app. right. apply in_or_app. left. exact Ht. }
    lia.
Qed.

Lemma nc_len G OUT es hj : (length es <= 4)%nat -> (length hj <= 4)%nat ->
  (length (rv_nc (view_of G OUT es hj)) <= NC_MAX)%nat.
Proof.
  intros He Hh. unfold view_of. cbn [rv_nc length]. rewrite length_app.
  assert (E1 : forall l : list rentry, (length (concat (map entry_nc l)) <= 2 * length l)%nat).
  { induction l as [|e l IH]; [cbn; lia|]. cbn [map concat]. rewrite length_app.
    assert (length (entry_nc e) <= 2)%nat by (unfold entry_nc; destruct (re_cap e =? 0), (re_hp e =? 0); cbn; lia).
    cbn [length]. lia. }
  assert (E2 : forall l : list (hsrc * nat), (length (concat (map (fun p => src_nc (fst p)) l)) <= 4 * length l)%nat).
  { induction l as [|p l IH]; [cbn; lia|]. cbn [map concat]. rewrite length_app.
    assert (length (src_nc (fst p)) <= 4)%nat.
    { unfold src_nc, arr_nc.
      destruct (hl_cap (hs_pending (fst p)) =? 0), (hl_cap (hs_expected (fst p)) =? 0), (hl_cap (hs_held (fst p)) =? 0);
        cbn; lia. }
    cbn [length]. lia. }
  pose proof (E1 es). pose proof (E2 hj). unfold NC_MAX. lia.
Qed.

Lemma mis3_keep V L A V' L' A' b b' (D : list (Z * Z)) (P : sptr -> Prop) :
  mis_nc V L (p3_mis b) -> res_ok_pack3 A b -> res_ok_pack3 A' b' -> List.NoDup (map fst (blocks L' A')) ->
  (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') -> In (ptr_addr L p) (rv_nc V) ->
     ~ In (ptr_addr L p) (map fst D) -> In (ptr_addr L' p) (rv_nc V')) ->
  (forall e, In e (p3_mis b') -> (In e (p3_mis b) /\ ~ In (ptr_addr L (fst e)) (map fst D)) \/ P (fst e)) ->
  (forall p, P p -> In (ptr_addr L' p) (rv_nc V')) ->
  mis_nc V' L' (p3_mis b').
Proof.
  intros (HI & _) HA HA' HN HK HS HP.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  pose proof HA' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HM' & _).
  pose proof HM' as (_ & HU' & _).
  split.
  - intros a Ha. unfold mis_addrs in Ha. apply in_map_iff in Ha as (e & <- & He).
    destruct (HU' e He) as (_ & n' & Hn').
    destruct (HS e He) as [(Ho & Hd)|Hp]; [|exact (HP _ Hp)].
    destruct (HU e Ho) as (_ & n & Hn).
    apply (HK (fst e) n n' Hn Hn'); [|exact Hd].
    apply HI. unfold mis_addrs. exact (in_map (fun e0 => ptr_addr L (fst e0)) _ e Ho).
  - exact (mis_nodup L' A' (p3_mis b') (p3_mcap b') HN HM').
Qed.

Definition cred3 (pl : list byte) (k k' : Z) (V V' : rview) (ks : list Z) : Prop :=
  (forall c, 0 <= c < 49 ->
     bcnt c ks + ek_c V' c + prom_c (rv_pend V') c + cons_c pl k c <= ek_c V c + prom_c (rv_pend V) c + cons_c pl k' c) /\
  zsum (fun n => n) ks + ek_b V' + promb (rv_pend V') + consb pl k <= ek_b V + promb (rv_pend V) + consb pl k'.

Lemma cred3_step NW pl k k' V L A b al alb V' ks : RI3_ledger NW pl k V L A b al alb -> cred3 pl k k' V V' ks ->
  (forall c, 0 <= c < 49 -> znth c al + bcnt c ks + ek_c V' c + prom_c (rv_pend V') c <= cons_c pl k' c) /\
  alb + zsum (fun n => n) ks + ek_b V' + promb (rv_pend V') <= consb pl k'.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _ & HQ) (C1 & C2). split; [|lia].
  intros c Hc. destruct (HQ c Hc) as (_ & _ & H3). pose proof (C1 c Hc). lia.
Qed.

Theorem step3 E k k' V L A b al alb V' L' A' b' ks dl db (D : list (Z * Z)) (P : sptr -> Prop) :
  RI3_ledger rv_wt (ss_pl E) k V L A b al alb -> res_ok_pack3 A b -> Forall (fun n => 0 <= n) ks ->
  res_ok_pack3 A' b' -> p3_cap b' = p3_cap b -> p3_mcap b' = p3_mcap b -> length (p3_live b') = 49%nat ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b') <= znth c (p3_live b) + bcnt c ks + dl c) ->
  p3_bytes b' <= p3_bytes b + zsum (fun n => n) ks + db ->
  (forall e, In e (p3_mis b') -> (In e (p3_mis b) /\ ~ In (ptr_addr L (fst e)) (map fst D)) \/ P (fst e)) ->
  (forall p, P p -> In (ptr_addr L' p) (rv_nc V')) ->
  List.NoDup (map fst (blocks L' A')) ->
  (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') -> In (ptr_addr L p) (rv_nc V) ->
     ~ In (ptr_addr L p) (map fst D) -> In (ptr_addr L' p) (rv_nc V')) ->
  (length (rv_nc V') <= NC_MAX)%nat ->
  (forall c, 0 <= c < 49 -> nc_cnt V L A c + dl c <= nc_cnt V' L' A' c) -> ncs V L A + db <= ncs V' L' A' ->
  ncs V' L' A' <= rv_wt V' ->
  rv_wt V' <= rv_wt V + NC_PER * zlen ks + DATA_PER * (cdat (ss_pl E) k' - cdat (ss_pl E) k) ->
  cred3 (ss_pl E) k k' V V' ks -> Forall (fun n => 0 <= n) (rv_ek V') -> RI3_reply E k' V' L' A'.
Proof.
  intros HL HA Hks HA' Hc Hm Hl Hlive Hby HS HP HN HK HN' HC' HB' HW1' HW' HCR HE'.
  destruct (cred3_step _ _ _ _ _ _ _ _ _ _ _ _ HL HCR) as (HP1 & HP2).
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HW2 & _ & HMis & _).
  hnf. exists b', (al_add al ks), (alb + zsum (fun n => n) ks). split; [exact HA'|].
  apply (ledger3_call rv_wt (ss_pl E) k V L A b al alb k' V' L' A' b' ks dl db HL Hks); try assumption.
  - split; [exact HN'|]. split; [exact HC'|]. split; [exact HB'|]. split; [exact HW1'|].
    split; [unfold NC_PER, DATA_PER in *; lia|]. split; [exact HP1|]. split; [exact HP2|exact HE'].
  - exact (mis3_keep V L A V' L' A' b b' D P HMis HA HA' HN HK HS HP).
Qed.

Fixpoint inplace (qs : list sptr) (j : nat) (tr : trF) (p : sptr) : Prop :=
  match tr with
  | [] => False
  | RMalloc _ :: r => inplace qs (S j) r p
  | RFree _ _ :: r => inplace qs j r p
  | RRealloc _ _ a :: r => (p = resolveF qs a /\ p = nth j qs (SP 0 0)) \/ inplace qs (S j) r p
  end.

Definition touched (qs : list sptr) (tr : trF) (p : sptr) : Prop :=
  exists a, resolveF qs a = p /\ ((exists n, In (RFree n a) tr) \/ (exists k n, In (RRealloc k n a) tr)).

Lemma run3_mis_src2 qs b j tr e : In e (p3_mis (run3 qs b j tr)) ->
  (In e (p3_mis b) /\ ~ touched qs tr (fst e)) \/ inplace qs j tr (fst e).
Proof.
  revert b j. induction tr as [|ev tr IH]; intros b j He.
  - left. split; [exact He|]. intros (a & _ & [(n & [])|(k & n & [])]).
  - destruct ev as [n|n a|k n a]; cbn [run_from inplace] in *.
    + destruct (IH _ _ He) as [(H & Hn)|H]; [left|right; exact H]. split; [exact H|].
      intros (a & Ea & [(m & [X|X])|(k & m & [X|X])]).
      * discriminate X.
      * apply Hn. exists a. split; [exact Ea|]. left. exists m. exact X.
      * discriminate X.
      * apply Hn. exists a. split; [exact Ea|]. right. exists k, m. exact X.
    + destruct (IH _ _ He) as [(H & Hn)|H]; [left|right; exact H]. unfold pb3_free in H. cbn [p3_mis] in H.
      apply op7_mis_del_in in H as [H Hne]. split; [exact H|].
      intros (a' & Ea & [(m & [X|X])|(k & m & [X|X])]).
      * injection X as -> ->. exact (Hne (eq_sym Ea)).
      * apply Hn. exists a'. split; [exact Ea|]. left. exists m. exact X.
      * discriminate X.
      * apply Hn. exists a'. split; [exact Ea|]. right. exists k, m. exact X.
    + destruct (IH _ _ He) as [(H & Hn)|H]; [|right; right; exact H]. unfold pb3_realloc in H. cbn [p3_mis] in H.
      apply op7_mis_realloc_in in H as [(E1 & E2)|(H & Hne)]; [right; left; split; congruence|left].
      split; [exact H|].
      intros (a' & Ea & [(m & [X|X])|(k' & m & [X|X])]).
      * discriminate X.
      * apply Hn. exists a'. split; [exact Ea|]. left. exists m. exact X.
      * injection X as -> -> ->. exact (Hne (eq_sym Ea)).
      * apply Hn. exists a'. split; [exact Ea|]. right. exists k', m. exact X.
Qed.

Lemma sptr_of_at L A p n : List.NoDup (map fst (blocks L A)) -> In (p, n) (user_blocks A) ->
  sptr_of L A (ptr_addr L p) = p.
Proof.
  intros HN Hp.
  assert (Hb : In (ptr_addr L p, n) (blocks L A)) by exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hp).
  destruct (sptr_of_spec L A _ _ (proj2 (stdpp.base.NoDup_ListNoDup _) HN) Hb) as (Hs & Ea).
  assert (HN' : List.NoDup (map (fun b => ptr_addr L (fst b)) (user_blocks A))) by (unfold blocks in HN; rewrite map_map in HN; exact HN).
  pose proof (nodup_map_eq (fun b => ptr_addr L (fst b)) (user_blocks A) _ _ HN' Hs Hp Ea) as E.
  exact (f_equal fst E).
Qed.

Lemma mis_D L A qs b j tr (D : list (Z * Z)) e : res_ok_pack3 A b ->
  (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (map fst D) -> touched qs tr p) ->
  In e (p3_mis (run3 qs b j tr)) ->
  (In e (p3_mis b) /\ ~ In (ptr_addr L (fst e)) (map fst D)) \/ inplace qs j tr (fst e).
Proof.
  intros HA HD He. pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  destruct (run3_mis_src2 qs b j tr e He) as [(Hm & Hu)|Hi]; [left|right; exact Hi].
  split; [exact Hm|]. intros Hx. apply Hu. destruct (HU e Hm) as (_ & n & Hn). exact (HD _ _ Hn Hx).
Qed.

Lemma touched_at L A qs tr (D : list (Z * Z)) : List.NoDup (map fst (blocks L A)) ->
  (forall x, In x (map fst D) -> touched qs tr (sptr_of L A x)) ->
  forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (map fst D) -> touched qs tr p.
Proof. intros HN HD p n Hp Hx. rewrite <- (sptr_of_at L A p n HN Hp). exact (HD _ Hx). Qed.

Lemma touched_free qs tr n a : In (RFree n a) tr -> touched qs tr (resolveF qs a).
Proof. intros H. exists a. split; [reflexivity|]. left. exists n. exact H. Qed.

Lemma touched_realloc qs tr k n a : In (RRealloc k n a) tr -> touched qs tr (resolveF qs a).
Proof. intros H. exists a. split; [reflexivity|]. right. exists k, n. exact H. Qed.

Definition rIv (b bc : pbound3) : Prop :=
  p3_cap bc = p3_cap b /\ p3_mcap bc = p3_mcap b /\
  (forall c, 0 <= c < 49 -> znth c (p3_live bc) <= znth c (p3_live b) + 2) /\ p3_bytes bc <= p3_bytes b + 2 * NMAX /\
  (forall c, count_mis (p3_mis bc) c <= count_mis (p3_mis b) c).

Lemma rIv_refl b : rIv b b.
Proof. unfold rIv. split; [reflexivity|]. split; [reflexivity|]. split; [intros c _; lia|]. split; [unfold NMAX; lia|intros c; lia]. Qed.

Lemma rIv_malloc b n : length (p3_live b) = 49%nat -> 0 <= n <= 2 * NMAX -> rIv b (pb3_malloc b n).
Proof.
  intros Hl Hn. unfold rIv. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros c Hc. pose proof (live3_malloc b n c ltac:(lia) ltac:(lia)). pose proof (one_if_b c (band n)). lia.
  - unfold pb3_malloc. cbn [p3_bytes p3_mis]. split; [lia|intros c; lia].
Qed.

Lemma rIv_realloc b k n p q : length (p3_live b) = 49%nat -> 0 <= k <= n -> n - k <= 2 * NMAX ->
  rIv b (pb3_realloc b k n p q).
Proof.
  intros Hl Hk Hn. unfold rIv. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros c Hc. pose proof (live3_realloc b k n p q c Hl ltac:(lia) ltac:(lia) Hc).
    pose proof (one_if_b c (band n)). pose proof (one_if_b c (band k)). lia.
  - unfold pb3_realloc. cbn [p3_bytes p3_mis]. split; [lia|]. intros c. apply count_mis_realloc. lia.
Qed.

Lemma room3_rIv NW pl k V L A b al alb bc n : RI3_ledger NW pl k V L A b al alb -> rIv b bc -> 0 <= n <= NMAX ->
  room_pack3 bc n.
Proof.
  intros HL (H1 & H2 & H3 & H4 & H5) Hn. pose proof HL as (HCs & HMc & _).
  pose proof (AllocPackRoom.band_range n ltac:(lia)) as Bn.
  apply (room_pack3_of bc n BMAX NMAX).
  - rewrite H1, H2, HCs, HMc. apply CS_reply_capok3.
  - exact Hn.
  - pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL).
    assert (X : PB3_MAX + 3 * NMAX <= BMAX) by (apply Z.leb_le; vm_compute; reflexivity). lia.
  - rewrite H1. pose proof (H3 (band n) Bn). pose proof (op7_slack _ _ _ _ _ _ _ _ _ (band n) HL Bn). lia.
  - intros Hb. rewrite H2. pose proof (H5 (band n + 1)).
    pose proof (ledger3_mis _ _ _ _ _ _ _ _ _ (band n + 1) HL ltac:(lia)). lia.
Qed.

Lemma entry_tr C g : C = 0 \/ C = 16 ->
  op_add_tr (Some 0%nat) FIRST_FD 0 C g = RMalloc PARTIAL_BYTES :: (if C =? 0 then [RMalloc SRC_TABLE] else []).
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma op0_tr i FD N g : (i <> None -> 0 <= N < 4) ->
  op_add_tr i FD N 16 g = match i with Some _ => [RMalloc PARTIAL_BYTES] | None => [] end.
Proof.
  destruct i as [i|]; [|reflexivity]. intros H. destruct (H ltac:(discriminate)) as [_ HN].
  unfold op_add_tr, relay_add_tr. replace (N =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb]. rewrite orb_true_r. reflexivity.
Qed.

Lemma push_tr nm l x : list_push_tr (sh_of nm l) x =
  (if hl_n l =? hl_cap l then
     (if hl_cap l =? 0 then [RMalloc 128] else [RRealloc (16 * hl_cap l) (32 * hl_cap l) (nm (hl_v l))])
   else []) ++ [RMalloc (Z.of_nat (length x) + 1)].
Proof. unfold list_push_tr, list_grow_tr, sh_n, hl_n, sh_of. cbn [sh_recs sh_cap sh_v]. rewrite length_map. reflexivity. Qed.

Fixpoint fsz (tr : trF) : list Z :=
  match tr with
  | [] => []
  | RFree n _ :: r => n :: fsz r
  | _ :: r => fsz r
  end.

Lemma fsz_app t1 t2 : fsz (t1 ++ t2) = fsz t1 ++ fsz t2.
Proof. induction t1 as [|e t1 IH]; [reflexivity|]. destruct e; cbn [app fsz]; rewrite IH; reflexivity. Qed.

Lemma frees_dl tr c : Forall ev_free tr -> tr_dl tr c = - bcnt c (fsz tr).
Proof.
  induction tr as [|e tr IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [He H].
  destruct e as [n|n a|k n a]; cbn [ev_free] in He; try contradiction.
  unfold tr_dl in *. cbn [fsz]. rewrite zsum_cons, bcnt_cons, IH by exact H. cbn [ev_dl]. lia.
Qed.

Lemma frees_db tr : Forall ev_free tr -> tr_db tr = - zsum (fun n => n) (fsz tr).
Proof.
  induction tr as [|e tr IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [He H].
  destruct e as [n|n a|k n a]; cbn [ev_free] in He; try contradiction.
  unfold tr_db in *. cbn [fsz]. rewrite !zsum_cons, IH by exact H. cbn [ev_db]. lia.
Qed.

Lemma frees_ok tr : Forall ev_free tr -> Forall (fun n => 0 <= n) (fsz tr) -> Forall ev_ok tr.
Proof.
  induction tr as [|e tr IH]; intros H Hn; [constructor|]. apply Forall_cons_iff in H as [He H].
  destruct e as [n|n a|k n a]; cbn [ev_free] in He; try contradiction.
  cbn [fsz] in Hn. apply Forall_cons_iff in Hn as [Hn0 Hn]. constructor; [exact Hn0|exact (IH H Hn)].
Qed.

Lemma frees_grow tr : Forall ev_free tr -> Forall ev_grow tr.
Proof.
  intros H. apply Forall_forall. intros e He. rewrite Forall_forall in H. pose proof (H e He).
  destruct e; cbn [ev_free ev_grow] in *; tauto.
Qed.

Lemma frees_inplace qs j tr p : Forall ev_free tr -> ~ inplace qs j tr p.
Proof.
  revert j. induction tr as [|e tr IH]; intros j H; [intros []|]. apply Forall_cons_iff in H as [He H].
  destruct e as [n|n a|k n a]; cbn [ev_free] in He; try contradiction. cbn [inplace]. exact (IH j H).
Qed.

Lemma fsz_recs rs : fsz (recs_drop_tr rs) = map rec_len rs.
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. unfold recs_drop_tr in *. cbn [map concat].
  change (rec_drop_tr r) with [RFree (rec_len r) (fst r)]. cbn [app fsz]. rewrite IH. reflexivity.
Qed.

Lemma rec_len_pos r : 1 <= rec_len r.
Proof. unfold rec_len. lia. Qed.

Lemma ends_free nm gone P rs d : Forall ev_free (check_shape_ends_tr nm gone P rs d) /\
  Forall (fun n => 1 <= n) (fsz (check_shape_ends_tr nm gone P rs d)).
Proof.
  assert (F : forall ds, Forall (fun n => 1 <= n) (fsz (recs_drop_tr ds))).
  { intros ds. rewrite fsz_recs. apply Forall_forall. intros n Hn. apply in_map_iff in Hn as (r & <- & _).
    apply rec_len_pos. }
  unfold check_shape_ends_tr. destruct (gone =? 0).
  - destruct (ends_run P rs d (want_of P rs)) as [[[x ds] y]|].
    + split; [apply recs_drop_free|apply F].
    + split; constructor.
  - split; [apply recs_drop_free|apply F].
Qed.

Lemma hlist_free_free nm l : Forall ev_free (hlist_free_tr nm l).
Proof.
  unfold hlist_free_tr, list_free_tr. apply Forall_app. split; [apply recs_drop_free|].
  destruct (sh_cap (sh_of nm l) =? 0); repeat constructor.
Qed.

Lemma reset_free nm h : Forall ev_free (source_reset_tr nm h).
Proof.
  unfold source_reset_tr. repeat (apply Forall_app; split; [apply hlist_free_free|]). repeat constructor.
Qed.

Definition cap_part (l : hlist) : list Z := if hl_cap l =? 0 then [] else [16 * hl_cap l].

Lemma fsz_hl nm l : fsz (hlist_free_tr nm l) = map rec_len (List.rev (map (shr nm) (hl_recs l))) ++ cap_part l.
Proof.
  unfold hlist_free_tr, list_free_tr, cap_part, sh_of. cbn [sh_recs sh_cap sh_v]. rewrite fsz_app, fsz_recs.
  destruct (hl_cap l =? 0); reflexivity.
Qed.

Lemma fsz_reset nm h : fsz (source_reset_tr nm h) =
  fsz (hlist_free_tr nm (hs_pending h)) ++ fsz (hlist_free_tr nm (hs_expected h)) ++
  fsz (hlist_free_tr nm (hs_held h)) ++ [PARTIAL_BYTES].
Proof. unfold source_reset_tr. rewrite !fsz_app. reflexivity. Qed.

Lemma arr_cap_sum (g : Z -> Z) l : zsum (fun t => g (snd t)) (arr_sz l) = zsum g (cap_part l).
Proof. unfold arr_sz, cap_part. destruct (hl_cap l =? 0); reflexivity. Qed.

Lemma recs_part_nonneg (g : Z -> Z) nm l : (forall x, 1 <= x -> 0 <= g x) ->
  0 <= zsum g (map rec_len (List.rev (map (shr nm) (hl_recs l)))).
Proof.
  intros Hg. apply zsum_nonneg. intros x Hx. apply Hg. apply in_map_iff in Hx as (r & <- & _). apply rec_len_pos.
Qed.

Lemma reset_sum (g : Z -> Z) nm h : (forall x, 1 <= x -> 0 <= g x) ->
  zsum (fun t => g (snd t)) (src_dels h) <= zsum g (fsz (source_reset_tr nm h)).
Proof.
  intros Hg. rewrite fsz_reset, !fsz_hl. unfold src_dels. rewrite !zsum_app, !arr_cap_sum.
  pose proof (recs_part_nonneg g nm (hs_pending h) Hg). pose proof (recs_part_nonneg g nm (hs_expected h) Hg).
  pose proof (recs_part_nonneg g nm (hs_held h) Hg).
  change (zsum (fun t => g (snd t)) [(hs_partial h, PARTIAL_BYTES)]) with (g PARTIAL_BYTES + 0).
  change (zsum g [PARTIAL_BYTES]) with (g PARTIAL_BYTES + 0). lia.
Qed.

Lemma hl_free_at nm l x : In x (map fst (arr_sz l)) -> In (RFree (16 * hl_cap l) (nm x)) (hlist_free_tr nm l).
Proof.
  unfold arr_sz. destruct (hl_cap l =? 0) eqn:E; [intros []|]. intros [<-|[]].
  unfold hlist_free_tr, list_free_tr, sh_of. cbn [sh_cap sh_v sh_recs]. rewrite E. apply in_or_app. right.
  left. reflexivity.
Qed.

Lemma reset_free_at nm h x : In x (map fst (src_dels h)) -> exists m, In (RFree m (nm x)) (source_reset_tr nm h).
Proof.
  unfold src_dels, source_reset_tr. rewrite !map_app. intros Hx. rewrite !in_app_iff in Hx.
  destruct Hx as [Hx|[[<-|[]]|[Hx|Hx]]].
  - exists (16 * hl_cap (hs_pending h)). apply in_or_app. left. exact (hl_free_at nm _ x Hx).
  - exists 6000. rewrite !in_app_iff. right. right. right. left. reflexivity.
  - exists (16 * hl_cap (hs_expected h)). rewrite !in_app_iff. right. left. exact (hl_free_at nm _ x Hx).
  - exists (16 * hl_cap (hs_held h)). rewrite !in_app_iff. right. right. left. exact (hl_free_at nm _ x Hx).
Qed.

Lemma cap_part_nonneg l : (hl_cap l <> 0 -> 0 <= 16 * hl_cap l) -> Forall (fun n => 0 <= n) (cap_part l).
Proof.
  intros H. unfold cap_part. destruct (Z.eqb_spec (hl_cap l) 0) as [E|E]; repeat constructor. exact (H E).
Qed.

Lemma reset_nonneg nm h : (forall t, In t (src_dels h) -> 0 <= snd t) ->
  Forall (fun n => 0 <= n) (fsz (source_reset_tr nm h)).
Proof.
  intros Hd.
  assert (C : forall l, (forall t, In t (arr_sz l) -> In t (src_dels h)) -> Forall (fun n => 0 <= n) (cap_part l)).
  { intros l Hl. apply cap_part_nonneg. intros Hne. apply (Hd (hl_v l, 16 * hl_cap l)). apply Hl.
    unfold arr_sz. rewrite (proj2 (Z.eqb_neq _ _) Hne). left. reflexivity. }
  assert (R : forall l, Forall (fun n => 0 <= n) (map rec_len (List.rev (map (shr nm) (hl_recs l))))).
  { intros l. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (r & <- & _). pose proof (rec_len_pos r).
    lia. }
  rewrite fsz_reset, !fsz_hl. unfold src_dels in C.
  repeat (apply Forall_app; split).
  - apply R.
  - apply C. intros t Ht. apply in_or_app. left. exact Ht.
  - apply R.
  - apply C. intros t Ht. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Ht.
  - apply R.
  - apply C. intros t Ht. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Ht.
  - repeat constructor. unfold PARTIAL_BYTES. lia.
Qed.

Definition ptr_keep (D : list (Z * Z)) (V : rview) (L : layout) (A : astate) (V' : rview) (L' : layout) (A' : astate)
    : Prop :=
  forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') -> In (ptr_addr L p) (rv_nc V) ->
    ~ In (ptr_addr L p) (map fst D) -> In (ptr_addr L' p) (rv_nc V').

Lemma mis_nil_D qs b j tr L e : In e (p3_mis (run3 qs b j tr)) ->
  (In e (p3_mis b) /\ ~ In (ptr_addr L (fst e)) (map fst (@nil (Z * Z)))) \/ inplace qs j tr (fst e).
Proof.
  intros He. destruct (run3_mis_src2 qs b j tr e He) as [(Hm & _)|Hi]; [left|right; exact Hi].
  split; [exact Hm|intros []].
Qed.

Lemma res_tr_weaken F (P Q : layout -> astate -> list sptr -> Prop) A tr :
  res_tr F P A tr -> (forall L' A' qs, P L' A' qs -> Q L' A' qs) -> res_tr F Q A tr.
Proof.
  intros (bnd & H1 & H2 & H3) HPQ. exists bnd. split; [exact H1|]. split; [exact H2|].
  intros L' A' qs Hq H. apply HPQ. exact (H3 L' A' qs Hq H).
Qed.

Lemma nc_move_adds_in V L A V' L' A' dels adds t : nc_move V L A V' L' A' dels adds -> In t adds ->
  In (fst t) (rv_nc V').
Proof.
  intros (R & gone & B & X & Y & _ & HV' & _) Ht. apply (Permutation_in _ (Permutation_sym HV')).
  apply in_or_app. right. apply in_map. exact Ht.
Qed.

Lemma tr_dl_mallocs ns c : tr_dl (map RMalloc ns) c = bcnt c ns.
Proof.
  unfold tr_dl, bcnt. induction ns as [|n ns IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons, IH. reflexivity.
Qed.

Lemma tr_db_mallocs ns : tr_db (map RMalloc ns) = zsum (fun n => n) ns.
Proof.
  unfold tr_db. induction ns as [|n ns IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons, IH. reflexivity.
Qed.

Lemma mallocs_ok ns : Forall (fun n => 0 <= n) ns -> Forall ev_ok (map RMalloc ns).
Proof. intros H. induction H as [|n ns Hn _ IH]; constructor; [exact Hn|exact IH]. Qed.

Lemma mallocs_inplace qs j ns p : ~ inplace qs j (map RMalloc ns) p.
Proof. revert j. induction ns as [|n ns IH]; intros j; [intros []|]. cbn [map inplace]. apply IH. Qed.

Lemma dl_adds adds c : dl_of [] adds c = bcnt c (map snd adds).
Proof.
  unfold dl_of, bcnt. induction adds as [|t adds IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons.
  rewrite zsum_nil in *. cbv beta. lia.
Qed.

Lemma db_adds adds : db_of [] adds = zsum (fun n => n) (map snd adds).
Proof.
  unfold db_of. induction adds as [|t adds IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons.
  rewrite zsum_nil in *. cbv beta. lia.
Qed.

Lemma mallocs_room NW pl k V L A b al alb qs ns : RI3_ledger NW pl k V L A b al alb ->
  Forall (fun n => 0 <= n <= NMAX) ns -> (length ns <= 2)%nat -> room3 qs b 0 (map RMalloc ns).
Proof.
  intros HL Hns Hlen. pose proof HL as (_ & _ & _ & HlL & _).
  destruct ns as [|n1 [|n2 [|n3 ns]]]; cbn [map room_from]; [exact I| | |cbn [length] in Hlen; lia].
  - apply Forall_cons_iff in Hns as [H1 _]. split; [|exact I].
    exact (room3_rIv _ _ _ _ _ _ b al alb b n1 HL (rIv_refl b) H1).
  - apply Forall_cons_iff in Hns as [H1 Hns]. apply Forall_cons_iff in Hns as [H2 _].
    split; [exact (room3_rIv _ _ _ _ _ _ b al alb b n1 HL (rIv_refl b) H1)|].
    split; [|exact I]. apply (room3_rIv _ _ _ _ _ _ b al alb (pb3_malloc b n1) n2 HL); [|exact H2].
    apply rIv_malloc; [exact HlL|unfold NMAX in *; lia].
Qed.

Theorem mallocs_res3 E k k' V L A ns : RI3_reply E k V L A -> Forall (fun n => 0 <= n <= NMAX) ns ->
  (length ns <= 2)%nat ->
  res_tr pack3_form (fun L' A' qs => forall V' adds, map snd adds = ns -> nc_move V L A V' L' A' [] adds ->
      List.NoDup (map fst (blocks L' A')) -> ptr_keep [] V L A V' L' A' -> (length (rv_nc V') <= NC_MAX)%nat ->
      ncs V' L' A' <= rv_wt V' -> rv_wt V' <= rv_wt V + DATA_PER * (cdat (ss_pl E) k' - cdat (ss_pl E) k) ->
      cred3 (ss_pl E) k k' V V' [] -> Forall (fun n => 0 <= n) (rv_ek V') -> RI3_reply E k' V' L' A')
    A (map RMalloc ns).
Proof.
  intros (b & al & alb & HR & HL) Hns Hlen. pose proof HL as (_ & _ & _ & HlL & _).
  assert (Hns0 : Forall (fun n => 0 <= n) ns)
    by (rewrite Forall_forall in *; intros n Hn; pose proof (Hns n Hn); lia).
  exists b. split; [exact HR|]. split.
  - intros qs _. rewrite roomF3. exact (mallocs_room _ _ _ _ _ _ b al alb qs ns HL Hns Hlen).
  - intros L' A' qs _ HA' V' adds Hsnd HM HND HK HN' HW1 HW HCR HE'. rewrite runF3 in HA'.
    destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
    apply (step3 E k k' V L A b al alb V' L' A' (run3 qs b 0 (map RMalloc ns)) [] (dl_of [] adds) (db_of [] adds)
      [] (inplace qs 0 (map RMalloc ns)) HL HR (Forall_nil _) HA'); try assumption.
    + apply run3_cap.
    + apply run3_mcap.
    + rewrite run3_len. exact HlL.
    + intros c Hc. rewrite (run3_live qs b 0 _ c HlL (mallocs_ok ns Hns0) Hc), tr_dl_mallocs, dl_adds, Hsnd.
      change (bcnt c []) with 0. lia.
    + rewrite run3_bytes, tr_db_mallocs, db_adds, Hsnd, zsum_nil. lia.
    + intros e He. exact (mis_nil_D qs b 0 _ L e He).
    + intros p Hp. exfalso. exact (mallocs_inplace qs 0 ns p Hp).
    + change (zlen []) with 0. lia.
Qed.

Theorem frees_res3 E k V L A tr : RI3_reply E k V L A -> Forall ev_free tr ->
  res_tr pack3_form (fun L' A' qs => forall V' dels, Forall (fun n => 0 <= n) (fsz tr) ->
      (forall c, 0 <= c < 49 -> zsum (fun t => one_if c (band (snd t))) dels <= bcnt c (fsz tr)) ->
      zsum snd dels <= zsum (fun n => n) (fsz tr) ->
      (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (map fst dels) -> exists m, In (RFree m (Known p)) tr) ->
      nc_move V L A V' L' A' dels [] ->
      List.NoDup (map fst (blocks L' A')) -> ptr_keep dels V L A V' L' A' -> (length (rv_nc V') <= NC_MAX)%nat ->
      ncs V' L' A' <= rv_wt V' -> rv_wt V' <= rv_wt V -> cred3 (ss_pl E) k k V V' [] ->
      Forall (fun n => 0 <= n) (rv_ek V') -> RI3_reply E k V' L' A')
    A tr.
Proof.
  intros (b & al & alb & HR & HL) Hf. pose proof HL as (_ & _ & _ & HlL & _).
  exists b. split; [exact HR|]. split; [intros qs _; apply roomF_frees; exact Hf|].
  intros L' A' qs _ HA' V' dels Hn Hd1 Hd2 HDx HM HND HK HN' HW1 HW HCR HE'. rewrite runF3 in HA'.
  destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
  pose proof (frees_ok tr Hf Hn) as Hok.
  apply (step3 E k k V L A b al alb V' L' A' (run3 qs b 0 tr) [] (dl_of dels []) (db_of dels [])
    dels (inplace qs 0 tr) HL HR (Forall_nil _) HA'); try assumption.
  - apply run3_cap.
  - apply run3_mcap.
  - rewrite run3_len. exact HlL.
  - intros c Hc. rewrite (run3_live qs b 0 tr c HlL Hok Hc), (frees_dl tr c Hf). pose proof (Hd1 c Hc).
    unfold dl_of. rewrite zsum_nil. change (bcnt c []) with 0. lia.
  - rewrite run3_bytes, (frees_db tr Hf). unfold db_of. rewrite !zsum_nil. lia.
  - intros e He. apply (mis_D L A qs b 0 tr dels e HR); [|exact He].
    intros p n Hp Hx. destruct (HDx p n Hp Hx) as (m & Hin). exact (touched_free qs tr m _ Hin).
  - intros p Hp. exfalso. exact (frees_inplace qs 0 tr p Hf Hp).
  - change (zlen []) with 0. lia.
Qed.

Theorem push_res3 E k k' V L A l (x : list Z) :
  RI3_reply E k V L A -> List.NoDup (map fst (blocks L A)) -> 0 <= hl_n l <= hl_cap l -> hl_cap l <= 2 * OPS_MAX ->
  1 <= Z.of_nat (length x) <= WRITE_MAX ->
  res_tr pack3_form (fun L' A' qs => forall V' q1,
      (hl_n l = hl_cap l -> ptr_addr L' (resolveF qs (Ret 0)) = q1) ->
      nc_move V L A V' L' A' (grow_dels (hl_v l) (hl_n l) (hl_cap l)) (grow_adds q1 (hl_n l) (hl_cap l)) ->
      List.NoDup (map fst (blocks L' A')) -> ptr_keep (grow_dels (hl_v l) (hl_n l) (hl_cap l)) V L A V' L' A' ->
      (length (rv_nc V') <= NC_MAX)%nat ->
      ncs V' L' A' <= rv_wt V' ->
      rv_wt V' <= rv_wt V + NC_PER * zlen [Z.of_nat (length x) + 1] +
        DATA_PER * (cdat (ss_pl E) k' - cdat (ss_pl E) k) ->
      cred3 (ss_pl E) k k' V V' [Z.of_nat (length x) + 1] -> Forall (fun n => 0 <= n) (rv_ek V') ->
      RI3_reply E k' V' L' A')
    A (list_push_tr (sh_of (known_at L A) l) x).
Proof.
  intros (b & al & alb & HR & HL) HND0 HN HC Hx. pose proof HL as (_ & _ & _ & HlL & _).
  assert (Hn1 : 0 <= Z.of_nat (length x) + 1 <= NMAX) by (unfold NMAX, WRITE_MAX in *; lia).
  assert (Hks : Forall (fun n => 0 <= n) [Z.of_nat (length x) + 1]) by (repeat constructor; lia).
  rewrite push_tr. exists b. split; [exact HR|].
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [ENC|ENC]; [destruct (Z.eqb_spec (hl_cap l) 0) as [EC0|EC0]|];
    cbn [app].
  - split.
    + intros qs _. rewrite roomF3. cbn [room_from].
      split; [apply (room3_rIv _ _ _ _ _ _ b al alb b 128 HL (rIv_refl b)); unfold NMAX; lia|].
      split; [|exact I]. apply (room3_rIv _ _ _ _ _ _ b al alb (pb3_malloc b 128) _ HL); [|exact Hn1].
      apply rIv_malloc; [exact HlL|unfold NMAX; lia].
    + intros L' A' qs _ HA' V' q1 Hlink HM HND HK HN' HW1 HW HCR HE'. rewrite runF3 in HA'.
      assert (ED : grow_dels (hl_v l) (hl_n l) (hl_cap l) = []) by (unfold grow_dels; rewrite ENC, EC0; reflexivity).
      assert (EA : grow_adds q1 (hl_n l) (hl_cap l) = [(q1, 128)])
        by (unfold grow_adds; rewrite ENC, EC0; reflexivity).
      rewrite ED, EA in HM. rewrite ED in HK. destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
      apply (step3 E k k' V L A b al alb V' L' A' _ [Z.of_nat (length x) + 1] (dl_of [] [(q1, 128)])
        (db_of [] [(q1, 128)]) [] (inplace qs 0 [RMalloc 128; RMalloc (Z.of_nat (length x) + 1)]) HL HR Hks HA');
        try assumption.
      * apply run3_cap.
      * apply run3_mcap.
      * rewrite run3_len. exact HlL.
      * intros c Hc. rewrite (run3_live qs b 0 _ c HlL) by (first [exact Hc | repeat constructor; cbn [ev_ok]; lia]).
        unfold tr_dl, dl_of, bcnt. rewrite !zsum_cons, !zsum_nil. cbn [ev_dl snd]. lia.
      * rewrite run3_bytes. unfold tr_db, db_of. rewrite !zsum_cons, !zsum_nil. cbn [ev_db snd]. lia.
      * intros e He. exact (mis_nil_D qs b 0 _ L e He).
      * intros p Hp. cbn [inplace] in Hp. contradiction.
  - assert (H32 : 0 <= 32 * hl_cap l <= NMAX) by (unfold NMAX, OPS_MAX in *; lia).
    split.
    + intros qs _. rewrite roomF3. cbn [room_from].
      split; [exact (room3_rIv _ _ _ _ _ _ b al alb b _ HL (rIv_refl b) H32)|].
      split; [|exact I]. apply (room3_rIv _ _ _ _ _ _ b al alb _ _ HL); [|exact Hn1].
      apply rIv_realloc; [exact HlL|lia|unfold NMAX, OPS_MAX in *; lia].
    + intros L' A' qs _ HA' V' q1 Hlink HM HND HK HN' HW1 HW HCR HE'. rewrite runF3 in HA'.
      assert (ED : grow_dels (hl_v l) (hl_n l) (hl_cap l) = [(hl_v l, 16 * hl_cap l)]).
      { unfold grow_dels. rewrite ENC, Z.eqb_refl, (proj2 (Z.eqb_neq (hl_cap l) 0) EC0). reflexivity. }
      assert (EA : grow_adds q1 (hl_n l) (hl_cap l) = [(q1, 32 * hl_cap l)]).
      { unfold grow_adds. rewrite ENC, Z.eqb_refl, (proj2 (Z.eqb_neq (hl_cap l) 0) EC0). reflexivity. }
      rewrite ED, EA in HM. rewrite ED in HK. destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
      apply (step3 E k k' V L A b al alb V' L' A' _ [Z.of_nat (length x) + 1]
        (dl_of [(hl_v l, 16 * hl_cap l)] [(q1, 32 * hl_cap l)]) (db_of [(hl_v l, 16 * hl_cap l)] [(q1, 32 * hl_cap l)])
        [(hl_v l, 16 * hl_cap l)]
        (inplace qs 0 [RRealloc (16 * hl_cap l) (32 * hl_cap l) (known_at L A (hl_v l)); RMalloc (Z.of_nat (length x) + 1)])
        HL HR Hks HA'); try assumption.
      * apply run3_cap.
      * apply run3_mcap.
      * rewrite run3_len. exact HlL.
      * intros c Hc. rewrite (run3_live qs b 0 _ c HlL) by (first [exact Hc | repeat constructor; cbn [ev_ok]; lia]).
        unfold tr_dl, dl_of, bcnt. rewrite !zsum_cons, !zsum_nil. cbn [ev_dl snd]. lia.
      * rewrite run3_bytes. unfold tr_db, db_of. rewrite !zsum_cons, !zsum_nil. cbn [ev_db snd]. lia.
      * intros e He. apply (mis_D L A qs b 0 _ [(hl_v l, 16 * hl_cap l)] e HR); [|exact He].
        apply (touched_at L A qs _ _ HND0). intros y [Ey|[]]. cbn [fst] in Ey. subst y.
        exact (touched_realloc qs _ (16 * hl_cap l) (32 * hl_cap l) (known_at L A (hl_v l)) (in_eq _ _)).
      * intros p Hp. cbn [inplace] in Hp. destruct Hp as [(_ & Ep)|[]]. rewrite Ep.
        change (nth 0 qs (SP 0 0)) with (resolveF qs (Ret 0)). rewrite (Hlink ENC).
        apply (nc_move_adds_in _ _ _ _ _ _ _ _ (q1, 32 * hl_cap l) HM). left. reflexivity.
  - split.
    + intros qs _. rewrite roomF3. cbn [room_from]. split; [|exact I].
      exact (room3_rIv _ _ _ _ _ _ b al alb b _ HL (rIv_refl b) Hn1).
    + intros L' A' qs _ HA' V' q1 Hlink HM HND HK HN' HW1 HW HCR HE'. rewrite runF3 in HA'.
      assert (ED : grow_dels (hl_v l) (hl_n l) (hl_cap l) = [])
        by (unfold grow_dels; rewrite (proj2 (Z.eqb_neq _ _) ENC); reflexivity).
      assert (EA : grow_adds q1 (hl_n l) (hl_cap l) = [])
        by (unfold grow_adds; rewrite (proj2 (Z.eqb_neq _ _) ENC); reflexivity).
      rewrite ED, EA in HM. rewrite ED in HK. destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
      apply (step3 E k k' V L A b al alb V' L' A' _ [Z.of_nat (length x) + 1] (dl_of [] []) (db_of [] [])
        [] (inplace qs 0 [RMalloc (Z.of_nat (length x) + 1)]) HL HR Hks HA'); try assumption.
      * apply run3_cap.
      * apply run3_mcap.
      * rewrite run3_len. exact HlL.
      * intros c Hc. rewrite (run3_live qs b 0 _ c HlL) by (first [exact Hc | repeat constructor; cbn [ev_ok]; lia]).
        unfold tr_dl, dl_of, bcnt. rewrite !zsum_cons, !zsum_nil. cbn [ev_dl snd]. lia.
      * rewrite run3_bytes. unfold tr_db, db_of. rewrite !zsum_cons, !zsum_nil. cbn [ev_db snd]. lia.
      * intros e He. exact (mis_nil_D qs b 0 _ L e He).
      * intros p Hp. cbn [inplace] in Hp. contradiction.
Qed.
