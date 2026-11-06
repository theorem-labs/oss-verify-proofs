From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT AllocPack AllocPack3
  AllocPack3Room AllocBound SlotKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotRes SlotMove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c relay_event_b_c SlotOp7R3 SlotPass7RV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p7r_perm_in {X : Type} (l l' : list X) x : Permutation l l' -> In x l -> In x l'.
Proof. intros H Hx. eapply Permutation_in; [exact H|exact Hx]. Qed.

Lemma p7r_zsum_perm {X : Type} (f : X -> Z) l l' : Permutation l l' -> zsum f l = zsum f l'.
Proof.
  intros H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2].
  - reflexivity.
  - rewrite !zsum_cons, IH. reflexivity.
  - rewrite !zsum_cons. lia.
  - lia.
Qed.

Lemma p7r_zsum_le {X : Type} (f g : X -> Z) l : (forall x, In x l -> f x <= g x) -> zsum f l <= zsum g l.
Proof.
  induction l as [|x l IH]; intros H; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons.
  pose proof (H x (or_introl eq_refl)).
  assert (zsum f l <= zsum g l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma p7r_one_if_eq c : one_if c c = 1.
Proof. unfold one_if. rewrite Z.eqb_refl. reflexivity. Qed.

Definition p7r_asz (l : list (Z * Z)) (q : Z) : Z := zsum (fun t => if fst t =? q then snd t else 0) l.

Lemma p7r_sz_asz L A q : nc_sz L A q = p7r_asz (blocks L A) q.
Proof.
  unfold nc_sz, p7r_asz. induction (blocks L A) as [|t l IH]; [reflexivity|].
  cbn [List.filter]. rewrite (zsum_cons (fun t => if fst t =? q then snd t else 0)). cbv beta.
  destruct (fst t =? q); cbv iota; [rewrite zsum_cons|]; lia.
Qed.

Lemma p7r_asz_app l1 l2 q : p7r_asz (l1 ++ l2) q = p7r_asz l1 q + p7r_asz l2 q.
Proof. unfold p7r_asz. apply zsum_app. Qed.

Lemma p7r_asz_perm l l' q : Permutation l l' -> p7r_asz l q = p7r_asz l' q.
Proof. intros H. unfold p7r_asz. apply p7r_zsum_perm. exact H. Qed.

Lemma p7r_asz_none l q : (forall m, ~ In (q, m) l) -> p7r_asz l q = 0.
Proof.
  induction l as [|[p m] l IH]; intros H; [reflexivity|]. unfold p7r_asz in *. rewrite zsum_cons. cbn [fst snd].
  destruct (Z.eqb_spec p q) as [Ep|Ep].
  - subst p. exfalso. exact (H m (or_introl eq_refl)).
  - cbv iota. rewrite IH; [lia|]. intros m' Hm'. exact (H m' (or_intror Hm')).
Qed.

Lemma p7r_asz_nonneg l q : (forall t, In t l -> 0 <= snd t) -> 0 <= p7r_asz l q.
Proof.
  intros H. unfold p7r_asz. apply zsum_nonneg. intros t Ht. cbv beta. pose proof (H t Ht).
  destruct (fst t =? q); cbv iota; lia.
Qed.

Lemma p7r_asz_ge l t : In t l -> (forall u, In u l -> 0 <= snd u) -> snd t <= p7r_asz l (fst t).
Proof.
  induction l as [|u l IH]; intros Hin H; [destruct Hin|].
  assert (N : 0 <= p7r_asz l (fst t)) by (apply p7r_asz_nonneg; intros v Hv; exact (H v (or_intror Hv))).
  unfold p7r_asz in *. rewrite zsum_cons. cbv beta. destruct Hin as [Eu|Hin].
  - subst u. rewrite Z.eqb_refl. cbv iota. lia.
  - pose proof (IH Hin (fun v Hv => H v (or_intror Hv))). pose proof (H u (or_introl eq_refl)).
    destruct (fst u =? fst t); cbv iota; lia.
Qed.

Lemma p7r_fst_eq (l : list (Z * Z)) t u : List.NoDup (map fst l) -> In t l -> In u l -> fst t = fst u -> t = u.
Proof.
  induction l as [|v l IH]; intros HN Ht Hu He; [destruct Ht|].
  cbn [map] in HN. apply List.NoDup_cons_iff in HN as [Hv HN].
  destruct Ht as [Et|Ht], Hu as [Eu|Hu].
  - congruence.
  - subst t. exfalso. apply Hv. rewrite He. apply in_map. exact Hu.
  - subst u. exfalso. apply Hv. rewrite <- He. apply in_map. exact Ht.
  - apply IH; assumption.
Qed.

Lemma p7r_asz_nodup l t : List.NoDup (map fst l) -> In t l -> p7r_asz l (fst t) = snd t.
Proof.
  induction l as [|v l IH]; intros HN Ht; [destruct Ht|]. cbn [map] in HN.
  apply List.NoDup_cons_iff in HN as [Hv HN']. destruct Ht as [Et|Ht].
  - subst t. assert (Z0 : p7r_asz l (fst v) = 0).
    { apply p7r_asz_none. intros m Hm. apply Hv. change (fst v) with (fst (fst v, m)). apply in_map. exact Hm. }
    unfold p7r_asz in *. rewrite zsum_cons. cbv beta. rewrite Z.eqb_refl. cbv iota. lia.
  - assert (E : (fst v =? fst t) = false).
    { apply Z.eqb_neq. intros E. apply Hv. rewrite E. apply in_map. exact Ht. }
    pose proof (IH HN' Ht) as IH'. unfold p7r_asz in *. rewrite zsum_cons. cbv beta. rewrite E. cbv iota. lia.
Qed.

Lemma p7r_has_true L A c q : nc_has L A c q = true <-> exists m, In (q, m) (blocks L A) /\ band m = c.
Proof.
  unfold nc_has. rewrite existsb_exists. split.
  - intros ([p m] & Hin & H). apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1, H2. cbn [fst snd] in *.
    subst. exists m. split; [exact Hin|reflexivity].
  - intros (m & Hin & Hb). exists (q, m). split; [exact Hin|]. cbn [fst snd]. rewrite Z.eqb_refl, Hb, Z.eqb_refl.
    reflexivity.
Qed.

Lemma p7r_cnt_sum V L A c : nc_cnt V L A c = zsum (fun q => if nc_has L A c q then 1 else 0) (rv_nc V).
Proof.
  change (nc_cnt V L A c) with (Z.of_nat (length (List.filter (nc_has L A c) (rv_nc V)))).
  induction (rv_nc V) as [|x l IH]; [reflexivity|].
  cbn [List.filter]. rewrite zsum_cons. cbv beta. destruct (nc_has L A c x); cbv iota; cbn [length]; lia.
Qed.

Definition p7r_dl (dels adds : list (Z * Z)) (c : Z) : Z :=
  zsum (fun t => one_if c (band (snd t))) adds - zsum (fun t => one_if c (band (snd t))) dels.

Definition p7r_db (dels adds : list (Z * Z)) : Z := zsum snd adds - zsum snd dels.

Lemma p7r_grow V L A V' L' A' dels adds : nc_move V L A V' L' A' dels adds ->
  (forall c, nc_cnt V L A c + p7r_dl dels adds c <= nc_cnt V' L' A' c) /\
  ncs V L A + p7r_db dels adds <= ncs V' L' A' /\
  (forall a m, In a (rv_nc V) -> In (a, m) (blocks L A) -> In a (rv_nc V') \/ In a (map fst dels)).
Proof.
  intros (R & gone & B & X & Y & HV & HV' & HB & HB' & Hpos & Hdel & HdN & HdR & HY & Hg).
  assert (InB' : forall t, In t (B ++ adds ++ X) -> In t (blocks L' A')).
  { intros t Ht. exact (p7r_perm_in _ _ _ (Permutation_sym HB') Ht). }
  assert (Pos : forall t, In t (B ++ adds ++ X) -> 0 <= snd t).
  { intros [q m] Ht. exact (Hpos q m (InB' _ Ht)). }
  assert (PosA : forall t, In t adds -> 0 <= snd t).
  { intros t Ht. apply Pos. apply in_or_app. right. apply in_or_app. left. exact Ht. }
  assert (PosX : forall t, In t X -> 0 <= snd t).
  { intros t Ht. apply Pos. apply in_or_app. right. apply in_or_app. right. exact Ht. }
  split; [|split].
  - intros c. rewrite !p7r_cnt_sum. unfold p7r_dl.
    rewrite (p7r_zsum_perm _ _ _ HV), (p7r_zsum_perm _ _ _ HV'), !zsum_app, !zsum_map.
    assert (S1 : zsum (fun q => if nc_has L A c q then 1 else 0) R <=
                 zsum (fun q => if nc_has L' A' c q then 1 else 0) R).
    { apply p7r_zsum_le. intros p Hp. cbv beta. destruct (nc_has L A c p) eqn:E; cbv iota.
      - apply p7r_has_true in E as (m & Hm & Hb).
        assert (E' : nc_has L' A' c p = true).
        { apply p7r_has_true. exists m. split; [|exact Hb]. apply InB'. apply in_or_app. left.
          apply (p7r_perm_in _ _ _ HB) in Hm. apply in_app_or in Hm as [Hm|Hm]; [exact Hm|].
          exfalso. apply in_app_or in Hm as [Hm|Hm]; [exact (proj1 (HdR _ Hm) Hp)|exact (proj1 (HY _ Hm) Hp)]. }
        rewrite E'. cbv iota. lia.
      - destruct (nc_has L' A' c p); cbv iota; lia. }
    assert (S2 : zsum (fun t => if nc_has L A c (fst t) then 1 else 0) dels <=
                 zsum (fun t => one_if c (band (snd t))) dels).
    { apply p7r_zsum_le. intros t Ht. cbv beta. pose proof (one_if_b c (band (snd t))).
      destruct (nc_has L A c (fst t)) eqn:E; cbv iota; [|lia].
      apply p7r_has_true in E as (m & Hm & Hb). apply (p7r_perm_in _ _ _ HB) in Hm.
      apply in_app_or in Hm as [Hm|Hm]; [exfalso; exact (proj2 (HdR _ Ht) m Hm)|].
      apply in_app_or in Hm as [Hm|Hm]; [|exfalso; exact (proj2 (HY _ Hm) (in_map fst dels t Ht))].
      assert (Et : (fst t, m) = t) by (apply (p7r_fst_eq dels); [exact HdN|exact Hm|exact Ht|reflexivity]).
      replace (snd t) with m by (rewrite <- Et; reflexivity). rewrite Hb, p7r_one_if_eq. lia. }
    assert (S3 : zsum (fun q => if nc_has L A c q then 1 else 0) gone <= 0).
    { assert (zsum (fun q => if nc_has L A c q then 1 else 0) gone <= 0 * Z.of_nat (length gone)); [|lia].
      apply zsum_le_bound. intros g Hg'. cbv beta. destruct (nc_has L A c g) eqn:E; cbv iota; [|lia].
      apply p7r_has_true in E as (m & Hm & _). exfalso. exact (Hg g Hg' m Hm). }
    assert (S4 : zsum (fun t => one_if c (band (snd t))) adds <=
                 zsum (fun t => if nc_has L' A' c (fst t) then 1 else 0) adds).
    { apply p7r_zsum_le. intros t Ht. cbv beta. unfold one_if.
      destruct (Z.eqb_spec c (band (snd t))) as [E|E]; cbv iota.
      - assert (E' : nc_has L' A' c (fst t) = true).
        { apply p7r_has_true. exists (snd t). split; [|symmetry; exact E]. apply InB'. apply in_or_app. right.
          apply in_or_app. left. destruct t as [q m]. exact Ht. }
        rewrite E'. cbv iota. lia.
      - destruct (nc_has L' A' c (fst t)); cbv iota; lia. }
    cbv beta. lia.
  - unfold ncs, p7r_db. rewrite (p7r_zsum_perm _ _ _ HV), (p7r_zsum_perm _ _ _ HV'), !zsum_app, !zsum_map.
    assert (T1 : zsum (nc_sz L A) R <= zsum (nc_sz L' A') R).
    { apply p7r_zsum_le. intros p Hp. cbv beta.
      rewrite !p7r_sz_asz, (p7r_asz_perm _ _ _ HB), (p7r_asz_perm _ _ _ HB'), !p7r_asz_app.
      rewrite (p7r_asz_none dels p) by (intros m Hm; exact (proj1 (HdR _ Hm) Hp)).
      rewrite (p7r_asz_none Y p) by (intros m Hm; exact (proj1 (HY _ Hm) Hp)).
      pose proof (p7r_asz_nonneg adds p PosA). pose proof (p7r_asz_nonneg X p PosX). lia. }
    assert (T2 : zsum (fun t => nc_sz L A (fst t)) dels <= zsum snd dels).
    { apply p7r_zsum_le. intros t Ht. cbv beta.
      rewrite p7r_sz_asz, (p7r_asz_perm _ _ _ HB), !p7r_asz_app, (p7r_asz_nodup dels t HdN Ht).
      rewrite (p7r_asz_none B (fst t)) by exact (proj2 (HdR _ Ht)).
      rewrite (p7r_asz_none Y (fst t)) by (intros m Hm; exact (proj2 (HY _ Hm) (in_map fst dels t Ht))).
      lia. }
    assert (T3 : zsum (nc_sz L A) gone <= 0).
    { assert (zsum (nc_sz L A) gone <= 0 * Z.of_nat (length gone)); [|lia].
      apply zsum_le_bound. intros g Hg'. rewrite p7r_sz_asz, (p7r_asz_none _ g (Hg g Hg')). lia. }
    assert (T4 : zsum snd adds <= zsum (fun t => nc_sz L' A' (fst t)) adds).
    { apply p7r_zsum_le. intros t Ht. cbv beta. rewrite p7r_sz_asz. apply p7r_asz_ge.
      - apply InB'. apply in_or_app. right. apply in_or_app. left. exact Ht.
      - intros [q m] Hu. exact (Hpos q m Hu). }
    lia.
  - intros a m Ha Hb. apply (p7r_perm_in _ _ _ HV) in Ha. apply in_app_or in Ha as [Ha|Ha].
    + left. apply (p7r_perm_in _ _ _ (Permutation_sym HV')). apply in_or_app. left. exact Ha.
    + apply in_app_or in Ha as [Ha|Ha]; [right; exact Ha|]. exfalso. exact (Hg a Ha m Hb).
Qed.

Definition p7r_alt (a : adrF) (j : nat) : Prop := match a with Known _ => True | Ret i => (i < j)%nat end.

Lemma p7r_sl_wf : forall f mx no cap rem j (o : adrF), p7r_alt o j ->
  wf_from sptr j (fst (sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Ho; cbn [sl_run]; cbv zeta; [exact I|].
  destruct (rem <=? 0); [exact I|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (cap <? no + n).
  - cbn [fst]. destruct (cap =? 0); cbn [wf_from rets]; (split; [first [exact I|exact Ho]|]);
      rewrite Nat.add_1_r; apply IH; cbn [p7r_alt]; lia.
  - apply IH. exact Ho.
Qed.

Lemma p7r_rel_wf live mx CAP EL (o : adrF) : p7r_alt o 0 -> wf_from sptr 0 (relay_event_tr live mx 0 CAP EL 0 o).
Proof.
  intros Ho. unfold relay_event_tr, send_line_tr. destruct live; [exact (p7r_sl_wf _ _ _ _ _ 0 o Ho)|exact I].
Qed.

Lemma p7r_nret_cons e (tr : trF) : nretF (e :: tr) = (rets sptr e + nretF tr)%nat.
Proof. reflexivity. Qed.

Lemma p7r_room1 (p : sptr) qr (tr : trF) (bc : pbound3) : wf_from sptr 0 tr -> length qr = nretF tr ->
  room_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc room_pack3 (p :: qr) bc 1 (shift_tr sptr 1 tr) ->
  roomF pack3_form qr bc tr.
Proof.
  intros W Hl H.
  pose proof (room_shift pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc room_pack3 [p] qr [] tr bc 1 0 W
    ltac:(lia) eq_refl) as E.
  rewrite app_nil_r in E. exact (proj1 E H).
Qed.

Lemma p7r_run1 (p : sptr) qr (tr : trF) (bc : pbound3) : wf_from sptr 0 tr -> length qr = nretF tr ->
  run_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc (p :: qr) bc 1 (shift_tr sptr 1 tr) =
  runF pack3_form qr bc tr.
Proof.
  intros W Hl.
  pose proof (run_shift pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc [p] qr [] tr bc 1 0 W
    ltac:(lia) eq_refl) as E.
  rewrite app_nil_r in E. exact E.
Qed.

Lemma p7r_resolve1 (p : sptr) qr (a : adrF) : resolveF (p :: qr) (shift_addr sptr 1 a) = resolveF qr a.
Proof. destruct a; reflexivity. Qed.

Lemma op7_view_len G o es hj : (length es <= 4)%nat -> (length hj <= 4)%nat ->
  (length (rv_nc (view_of G o es hj)) <= NC_MAX)%nat.
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

Lemma op7_move_count V L A V' L' A' out CAP out' CAP' live :
  nc_move V L A V' L' A' (out_move_dels out CAP out' CAP') (out_move_adds out CAP out' CAP') ->
  (live = false -> out' = out /\ CAP' = CAP) -> 0 <= CAP ->
  (forall c, 0 <= c < 49 -> nc_cnt V L A c + op7_dl CAP CAP' c <= nc_cnt V' L' A' c) /\
  ncs V L A + (CAP' - CAP) <= ncs V' L' A' /\
  (forall a m, In a (rv_nc V) -> In (a, m) (blocks L A) -> a <> out \/ live = false -> In a (rv_nc V')).
Proof.
  intros HM HlF HC. revert HM. unfold out_move_dels, out_move_adds.
  destruct (out_same out CAP out' CAP') eqn:Hs; cbn [orb].
  - intros HM. pose proof (p7r_grow _ _ _ _ _ _ _ _ HM) as (G1 & G2 & G3).
    unfold out_same in Hs. apply andb_true_iff in Hs as [Hs1 Hs2]. apply Z.eqb_eq in Hs1, Hs2. subst out' CAP'.
    split; [|split].
    + intros c _. pose proof (G1 c) as G. unfold p7r_dl in G. rewrite !zsum_nil in G.
      unfold op7_dl. rewrite Z.eqb_refl. cbv iota. lia.
    + unfold p7r_db in G2. rewrite !zsum_nil in G2. lia.
    + intros a m Ha Hb _. destruct (G3 a m Ha Hb) as [H|H]; [exact H|]. cbn in H. contradiction.
  - destruct (Z.eqb_spec CAP 0) as [E0|E0]; cbv iota; intros HM;
      pose proof (p7r_grow _ _ _ _ _ _ _ _ HM) as (G1 & G2 & G3).
    + subst CAP. split; [|split].
      * intros c _. pose proof (G1 c) as G. unfold p7r_dl in G. rewrite ?zsum_cons, ?zsum_nil in G.
        cbv beta in G. cbn [snd] in G. pose proof (one_if_b c (band CAP')).
        unfold op7_dl. rewrite Z.eqb_refl. destruct (CAP' =? 0); cbv iota; lia.
      * unfold p7r_db in G2. rewrite ?zsum_cons, ?zsum_nil in G2. cbn [snd] in G2. lia.
      * intros a m Ha Hb _. destruct (G3 a m Ha Hb) as [H|H]; [exact H|]. cbn in H. contradiction.
    + split; [|split].
      * intros c _. pose proof (G1 c) as G. unfold p7r_dl in G. rewrite ?zsum_cons, ?zsum_nil in G.
        cbv beta in G. cbn [snd] in G.
        unfold op7_dl. rewrite (proj2 (Z.eqb_neq CAP 0) E0).
        destruct (Z.eqb_spec CAP' CAP) as [->|_]; cbv iota; lia.
      * unfold p7r_db in G2. rewrite ?zsum_cons, ?zsum_nil in G2. cbn [snd] in G2. lia.
      * intros a m Ha Hb Hor. destruct (G3 a m Ha Hb) as [H|H]; [exact H|].
        cbn in H. destruct H as [<-|[]]. exfalso. destruct Hor as [Hne|Hl]; [exact (Hne eq_refl)|].
        destruct (HlF Hl) as [-> ->]. unfold out_same in Hs. rewrite !Z.eqb_refl in Hs. cbn in Hs. discriminate.
Qed.

Theorem op7_res_s_RI3 : op7_res_s pack3_form RI3_reply.
Proof.
  intros E K K' L A EL live mx CAP G out es hj HRI HK1 HKK HnE HEL Hmx HCAP HND HO HO0.
  assert (HnE' : ss_n E < 67108864) by exact HnE.
  assert (HC' : CAP <= 536870912) by exact (proj2 HCAP).
  assert (HN : 2 * (EL + 1) <= 536879104) by lia.
  assert (HC2 : 0 <= CAP <= 536879104) by lia.
  destruct (op7_res3 E K K' (view_of G out es hj) L A EL live mx CAP out HRI ltac:(lia) (proj1 HEL) HN (proj1 Hmx)
    HC2 HND HO HO0) as (b & HR & ROOM & POST).
  unfold op7_S1, op7_S2, op7_S3, op7_RV_s.
  set (o := known_at L A out) in *.
  pose proof (p7r_rel_wf live mx CAP EL o I) as W.
  assert (F1 : relay_event_tr live mx 0 CAP EL 1 o = shift_tr sptr 1 (relay_event_tr live mx 0 CAP EL 0 o)).
  { rewrite (op7_shift_tr live mx 0 CAP EL 1 o). reflexivity. }
  assert (F2 : nretF (op7_trT EL live mx CAP o) = S (nretF (relay_event_tr live mx 0 CAP EL 0 o))).
  { unfold op7_trT. rewrite p7r_nret_cons, nret_app, F1, nret_shift. cbn [rets nret fold_right]. lia. }
  hnf. exists b. split; [exact HR|]. split.
  - intros qs _.
    pose proof (ROOM (List.repeat (SP 0 0) (nretF (op7_trT EL live mx CAP o))) ltac:(apply List.repeat_length))
      as R0.
    unfold roomF, room_run, op7_trT in R0. cbn [room_from] in R0.
    exact (conj (proj1 R0) I).
  - intros L1 A1 qm _ Hok1. hnf. exists (pb3_malloc b (EL + 1)). split; [exact Hok1|]. split.
    + intros qr Hqr.
      pose proof (ROOM (SP 0 0 :: qr) ltac:(cbn [length]; rewrite F2, Hqr; reflexivity)) as R1.
      unfold roomF, room_run, op7_trT in R1. cbn [room_from] in R1. destruct R1 as [_ R1].
      apply room_from_app in R1. destruct R1 as [R1 _]. rewrite F1 in R1.
      exact (p7r_room1 (SP 0 0) qr _ (pb3_malloc b (EL + 1)) W Hqr R1).
    + intros L2 A2 qr Hqr Hok2 p. hnf.
      exists (runF pack3_form qr (pb3_malloc b (EL + 1)) (relay_event_tr live mx 0 CAP EL 0 o)).
      split; [exact Hok2|]. split; [intros qf _; exact I|].
      intros L3 A3 qf _ Hok3 out' Hlv es' Hes' Hhj Hmv HlF Hpa HND3 Hwt1 Hwt2.
      pose proof (op7_move_count _ _ _ _ _ _ out CAP out' _ live Hmv HlF (proj1 HCAP)) as (MC1 & MC2 & MC3).
      apply (POST L3 A3 (p :: qr)).
      * cbn [length]; rewrite F2, Hqr; reflexivity.
      * rewrite op7_run_eq. cbn [nth]. rewrite F1, p7r_run1 by assumption. exact Hok3.
      * exact (op7_view_len G out' es' hj Hes' Hhj).
      * exact MC1.
      * exact MC2.
      * exact Hwt1.
      * change (nc_wt es' hj <= nc_wt es hj). lia.
      * reflexivity.
      * reflexivity.
      * exact HND3.
      * exact Hpa.
      * exact MC3.
      * intros Hl. destruct (Hlv Hl) as [_ Ha].
        assert (F3 : op7_outT live mx CAP EL o = shift_addr sptr 1 (relay_event_out live mx 0 CAP EL 0 o)).
        { unfold op7_outT. rewrite op7_shift_out. reflexivity. }
        rewrite F3, p7r_resolve1, Ha. cbn [rv_nc view_of In]. right. left. reflexivity.
Qed.
