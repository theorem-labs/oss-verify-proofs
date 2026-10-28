(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_depot_defs R_fs_defs RT_state RT_rep RT_facts0 RT_sep RT_facts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Definition upd_reg (r : regst) (i : nat) (st : ckst) : regst := mkReg (r_muser r) (r_mfa r) (upd (r_st r) i st) (r_fl r).

Definition mal_hit (Σ : rtsA) (c n : Z) (D' : depot) : rtsA :=
  let i := Z.to_nat (last (ca Σ c) 0) in
  mkRtsA (lay Σ) (fun c' => if c' =? c then upd_reg (pr Σ c) i (CkAlloc n) else pr Σ c')
    (fun c' => if c' =? c then removelast (ca Σ c) else ca Σ c') (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) D'
    (fs0 Σ) (fsc0 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (fs2 Σ) (ia_init Σ) (credit Σ - mcost n) ((p_ubeg (l_SB (lay Σ)) c i n, n) :: live Σ) (frames Σ) (arem (p_ubeg (l_SB (lay Σ)) c i n) (ann Σ)).

Lemma nth_error_upd_ck : forall (l : list ckst) i j x, nth_error (upd l i x) j = if Nat.eqb i j then (if Nat.ltb j (length l) then Some x else None) else nth_error l j.
Proof.
  intros l i j x. destruct (Nat.eqb_spec i j) as [->|Hne].
  - destruct (Nat.ltb_spec j (length l)) as [L|L]; [apply nth_error_upd_same; exact L|]. apply nth_error_None. rewrite upd_length. lia.
  - apply nth_error_upd_other. exact Hne.
Qed.

Lemma removelast_incl : forall {X} (l : list X) x, In x (removelast l) -> In x l.
Proof.
  intros X l. induction l as [|y l IH]; intros x H; [exact H|]. destruct l as [|z l]; [destruct H|].
  cbn [removelast] in H. destruct H as [<-|H]; [left; reflexivity | right; exact (IH x H)].
Qed.

Lemma app_removelast_last : forall {X} (l : list X) d, l <> [] -> l = removelast l ++ [last l d].
Proof. intros X l d H. apply app_removelast_last. exact H. Qed.

Lemma nodup_last_not_removelast : forall (l : list Z) d, List.NoDup l -> l <> [] -> ~ In (last l d) (removelast l).
Proof.
  intros l d Hnd Hne Hin. rewrite (app_removelast_last l d Hne) in Hnd. apply List.NoDup_remove_2 in Hnd. rewrite app_nil_r in Hnd.
  exact (Hnd Hin).
Qed.

Lemma sum_cls_ext : forall f g k, (forall j, (j <= k)%nat -> f (Z.of_nat j) = g (Z.of_nat j)) -> sum_cls f k = sum_cls g k.
Proof. intros f g k H. induction k as [|k IH]; [reflexivity|]. cbn [sum_cls]. rewrite H by lia. rewrite IH by (intros j Hj; apply H; lia). reflexivity. Qed.

Lemma dep_inv_bounds : forall D nl cr, dep_inv D -> dep_pot (d_n D) nl cr -> 0 <= nl -> 0 <= cr -> d_n D + 2 < 2 ^ 16 /\ d_tot D + 255 < 2 ^ 20.
Proof. intros D nl cr (_ & H1 & H2) HP Hnl Hcr. unfold dep_pot, DCOST, CREDIT_INIT in HP. lia. Qed.

Lemma dep_pot_malloc : forall D D' nl cr n, dep_step D D' -> dep_pot (d_n D) nl cr -> mcost n <= cr ->
  dep_pot (d_n D') (nl + 1) (cr - mcost n).
Proof. intros D D' nl cr n (_ & HS) HP HC. unfold dep_pot, mcost, DCOST, CREDIT_INIT in *. destruct (Z.leb_spec n 64512); lia. Qed.

Lemma dep_pot_free : forall D D' nl nl' cr, dep_step D D' -> dep_pot (d_n D) nl cr -> nl' + 1 <= nl -> dep_pot (d_n D') nl' cr.
Proof. intros D D' nl nl' cr (_ & HS) HP HL. unfold dep_pot, DCOST, CREDIT_INIT in *. lia. Qed.

Lemma mal_hit_eager : forall Σ c n D', rt_eager (mal_hit Σ c n D') = rt_eager Σ.
Proof.
  intros Σ c n D'. unfold rt_eager, mal_hit. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
  destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; reflexivity | reflexivity].
Qed.

Section Hit.
Variables (Σ : rtsA) (m : mem) (c n : Z) (D' : depot).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hne : ca Σ c <> [].
Hypothesis Hn : 1 <= n.
Hypothesis Hfit : rz_size n + n <= ClassSize c.
Hypothesis Hcls : c = ClassID (needed n).
Hypothesis Hlive : Z.of_nat (length (live Σ)) < LIVE_MAX.
Hypothesis Hcr : mcost n <= credit Σ.
Hypothesis HDok : depot_ok D' (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HDinv : dep_step (dep Σ) D'.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation i := (Z.to_nat (last (ca Σ c) 0)).

Lemma hit_entry : 0 <= last (ca Σ c) 0 < Z.of_nat (length (r_st (pr Σ c))) /\ nth_error (r_st (pr Σ c)) i = Some CkIdle
  /\ ~ In (last (ca Σ c) 0) (r_fl (pr Σ c)) /\ ~ In (last (ca Σ c) 0) (removelast (ca Σ c)).
Proof.
  pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (_ & _ & HC & _). destruct (HC c Hc) as (_ & Hnd & Hall).
  assert (Hin : In (last (ca Σ c) 0) (ca Σ c)) by (rewrite (app_removelast_last (ca Σ c) 0 Hne) at 2; apply in_or_app; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) Hall _ Hin) as (H1 & H2). split; [exact H1|]. split; [exact H2|].
  apply NoDup_ListNoDup in Hnd. split.
  - intros Hf. rewrite (app_removelast_last (ca Σ c) 0 Hne) in Hnd. rewrite <- app_assoc in Hnd. cbn [app] in Hnd.
    apply List.NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. right. exact Hf.
  - apply nodup_last_not_removelast; [|exact Hne]. apply (List.NoDup_app_remove_r _ _ Hnd).
Qed.

Lemma hit_reg_wf : reg_wf c (upd_reg (pr Σ c) i (CkAlloc n)).
Proof.
  pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  destruct hit_entry as (E1 & E2 & E3 & _).
  unfold upd_reg, reg_wf. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length.
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|].
  split; [exact W7|]. split; [exact W8|]. split.
  - apply Forall_forall. intros j Hj. destruct (proj1 (Forall_forall _ _) W9 j Hj) as (J1 & J2). split; [exact J1|].
    rewrite nth_error_upd_ck. destruct (Nat.eqb_spec i (Z.to_nat j)) as [E|E]; [|exact J2].
    exfalso. apply E3. assert (last (ca Σ c) 0 = j) by (apply Z2Nat.inj; lia). subst j. exact Hj.
  - split; [|exact W11]. apply Forall_forall. intros st Hst. apply (In_nth_error _ _) in Hst as (k & Hk). rewrite nth_error_upd_ck in Hk.
    destruct (Nat.eqb_spec i k) as [E|E].
    + destruct (Nat.ltb_spec k (length (r_st (pr Σ c)))); [injection Hk as <-; refine (conj _ (conj _ Hcls)); lia | discriminate].
    + exact (proj1 (Forall_forall _ _) W10 st (nth_error_In _ _ Hk)).
Qed.

Lemma hit_nth_cases : forall c' i' st, nth_error (r_st (pr (mal_hit Σ c n D') c')) i' = Some st ->
  (c' = c /\ i' = i /\ st = CkAlloc n) \/ (nth_error (r_st (pr Σ c')) i' = Some st /\ (c' <> c \/ i' <> i)).
Proof.
  intros c' i' st H. unfold mal_hit in H. cbn [pr] in H. destruct (Z.eqb_spec c' c) as [->|Hcc].
  - unfold upd_reg in H. cbn [r_st] in H. rewrite nth_error_upd_ck in H. destruct (Nat.eqb_spec i i') as [<-|Hii].
    + destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [injection H as <-; left; tauto | discriminate].
    + right. split; [exact H | right; intros E; apply Hii; symmetry; exact E].
  - right. split; [exact H | left; exact Hcc].
Qed.

Lemma hit_nth_keep : forall c' i' st, nth_error (r_st (pr Σ c')) i' = Some st -> st <> CkIdle ->
  nth_error (r_st (pr (mal_hit Σ c n D') c')) i' = Some st.
Proof.
  intros c' i' st H Hst. destruct hit_entry as (_ & E2 & _). unfold mal_hit. cbn [pr]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact H].
  unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec i i') as [<-|Hii]; [|exact H].
  rewrite E2 in H. injection H as <-. exfalso. exact (Hst eq_refl).
Qed.

Lemma hit_qent_ok : forall e, qent_ok Σ e -> qent_ok (mal_hit Σ c n D') e.
Proof.
  intros e [(c' & i' & Hc' & Hq & He)|X]; [left | right; exact X].
  exists c', i'. split; [exact Hc'|]. split; [|exact He]. apply hit_nth_keep; [exact Hq | discriminate].
Qed.

Theorem mal_hit_wf : rt_wf (mal_hit Σ c n D').
Proof using HA Hc Hne Hn Hfit Hcls Hlive Hcr HDok HDinv.
  pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12).
  destruct hit_entry as (E1 & E2 & E3 & E4). assert (POT' : dep_pot (d_n D') (Z.of_nat (length (live Σ)) + 1) (credit Σ - mcost n)) by exact (dep_pot_malloc (dep Σ) D' _ _ n HDinv W9 Hcr).
  pose proof (dep_inv_bounds D' _ _ (proj1 HDinv) POT' ltac:(lia) ltac:(lia)) as (B1 & B2).
  unfold rt_wf, mal_hit. cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fsc0 fs4 fs1 fs3 fs2 ia_init credit live frames ann].
  split; [exact W1|]. split.
  {
    unfold regs_wf. cbn [pr ca ca_init]. destruct W2 as (R1 & R2 & R3 & R4 & R5 & R6). split; [intros c' Hc'; destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact hit_reg_wf | exact (R1 c' Hc')]|].
    split; [intros c' Hc'; destruct (Z.eqb_spec c' c) as [->|Hcc]; [lia | exact (R2 c' Hc')]|].
    split; [|split; [intros Hi c'; destruct (Z.eqb_spec c' c) as [->|Hcc]; [rewrite (R4 Hi c); reflexivity | exact (R4 Hi c')]|split]].
    3:{   intros Hf. exfalso. apply Hne. exact (R4 Hf c). }
    2:{
      intros c' i' Hc' Hi'. destruct (Z.eqb_spec c' c) as [->|Hcc].
      - unfold upd_reg in Hi'. cbn [r_st r_fl] in Hi' |- *. rewrite nth_error_upd_ck in Hi'. destruct (Nat.eqb_spec i i') as [<-|Hii].
        + destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); discriminate.
        + pose proof (R5 c i' Hc Hi') as X. rewrite (app_removelast_last (ca Σ c) 0 Hne) in X. rewrite <- app_assoc in X.
          apply in_app_or in X as [X|X]; [apply in_or_app; left; exact X|]. cbn [app In] in X. destruct X as [X|X]; [|apply in_or_app; right; exact X].
          exfalso. apply Hii. rewrite X. apply Nat2Z.id.
      - exact (R5 c' i' Hc' Hi'). }
    intros c' Hc'. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact (R3 c' Hc')].
    destruct (R3 c Hc) as (C1 & C2 & C3). unfold upd_reg. cbn [r_st r_fl]. rewrite upd_length.
    assert (Hlr : length (ca Σ c) = (length (removelast (ca Σ c)) + 1)%nat) by (rewrite (app_removelast_last (ca Σ c) 0 Hne) at 1; rewrite length_app; reflexivity).
    split; [lia|]. split.
    - apply NoDup_ListNoDup in C2. apply NoDup_ListNoDup. rewrite (app_removelast_last (ca Σ c) 0 Hne) in C2.
      rewrite <- app_assoc in C2. cbn [app] in C2. apply List.NoDup_remove_1 in C2. exact C2.
    - apply Forall_forall. intros j Hj. destruct (proj1 (Forall_forall _ _) C3 j (removelast_incl _ _ Hj)) as (J1 & J2).
      split; [exact J1|]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec i (Z.to_nat j)) as [E|E]; [|exact J2].
      exfalso. apply E4. assert (last (ca Σ c) 0 = j) by (apply Z2Nat.inj; lia). subst j. exact Hj. }
  split.
  {
    unfold live_wf. cbn [pr live lay sec]. destruct W3 as (V1 & V2 & V3 & V4 & V5). split; [cbn [length]; lia|]. split.
    - apply NoDup_ListNoDup. apply NoDup_ListNoDup in V2. cbn [map fst]. constructor; [|exact V2].
      intros Hin. apply in_map_iff in Hin as ([p' n'] & Hp' & Hin). cbn [fst] in Hp'.
      pose proof (live_in_slot Σ m HA c i n) as _.
      destruct (geo_live Σ m HA p' n' Hin) as [(c' & i' & Hc' & Hn' & Ep & X1 & X2 & X3 & X4 & X5)|(s & Hs & _ & Hn' & Ep & X1 & X5)].
      + destruct (Z.eq_dec c' c) as [->|Hcc]; [destruct (Nat.eq_dec i' i) as [->|Hii]|].
        * rewrite E2 in Hn'. discriminate.
        * destruct (slot_apart Σ m HA c i c i' _ _ Hc Hc' E2 Hn' (or_intror (fun E => Hii (eq_sym E)))) as [Y|Y];
            unfold p_ubeg in *; pose proof (rz_facts n) as (_ & R); lia.
        * destruct (slot_apart Σ m HA c i c' i' _ _ Hc Hc' E2 Hn' (or_introl (fun E => Hcc (eq_sym E)))) as [Y|Y];
            unfold p_ubeg in *; pose proof (rz_facts n) as (_ & R); lia.
      + pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
        pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & Ha & _).
        pose proof (slot_geo Σ m HA c i _ Hc E2) as (S1 & S2 & S3 & _). pose proof (geo_prb Σ m HA) as (P1 & P2 & _).
        unfold apart, s_ubeg, p_ubeg, rb, kUserCap in *. pose proof (rz_facts n) as (_ & R). rewrite <- Hn' in X1.
        assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    - split; [|split; [|intros s Hs Hq; right; exact (V5 s Hs Hq)]].
      + intros p' n' [E|Hin].
        * injection E as <- <-. left. exists c, i. split; [exact Hc|]. split; [|reflexivity]. rewrite Z.eqb_refl. unfold upd_reg. cbn [r_st].
          rewrite nth_error_upd_ck, Nat.eqb_refl. destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [reflexivity | lia].
        * destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & Ep)|X]; [left|right; exact X]. exists c', i'. split; [exact Hc'|]. split; [|exact Ep].
          destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact Hn']. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
          destruct (Nat.eqb_spec i i') as [<-|Hii]; [rewrite E2 in Hn'; discriminate | exact Hn'].
      + intros c' i' n' Hc' Hn'. destruct (Z.eqb_spec c' c) as [->|Hcc].
        * unfold upd_reg in Hn'. cbn [r_st] in Hn'. rewrite nth_error_upd_ck in Hn'. destruct (Nat.eqb_spec i i') as [<-|Hii].
          -- destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [|discriminate]. injection Hn' as <-. left. reflexivity.
          -- right. exact (V4 c i' n' Hc' Hn').
        * right. exact (V4 c' i' n' Hc' Hn'). }
  split; [exact W4|]. split.
  {
    unfold quar_wf. cbn [ql qg pr lay]. destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). split; [exact Q1|]. split; [exact Q2|].
    split.
    { apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) Q3 b Hb) as (i' & Hi' & Eb). exists i'. split; [|exact Eb].
      destruct (Z.eqb_spec 24 c) as [Ec|Hcc]; [|exact Hi']. rewrite Ec in Hi'. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
      destruct (Nat.eqb_spec i i') as [Ei|Hii]; [rewrite <- Ei, E2 in Hi'; discriminate | exact Hi']. }
    split; [exact Q4|]. split; [exact Q5|].
    split; [apply Forall_forall; intros e He; exact (hit_qent_ok e (proj1 (Forall_forall _ _) Q6 e He))|]. split; [exact Q7|].
    intros c' i' Hc' Hb. destruct (hit_nth_cases c' i' CkBatch Hb) as [(_ & _ & X)|(X & _)]; [discriminate X | exact (Q8 c' i' Hc' X)]. }
  split.
  {
    destruct W6 as (F1 & F2 & F3 & F3b & F3c & F3d & F4 & F5 & F6 & F7 & F8).
    assert (Hm0 : 0 <= mcost n) by (unfold mcost, DCOST; destruct (n <=? 64512); lia).
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F3b|]. split; [exact F3c|]. split; [exact F3d|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|].
    split; [exact F7|]. intros k Hk. pose proof (F8 k Hk) as X. cbn [credit] in *.
    assert (fss_hint (fs_of {| lay := L; pr := fun c' : Z => if c' =? c then upd_reg (pr Σ c) i (CkAlloc n) else pr Σ c';
      ca := fun c' : Z => if c' =? c then removelast (ca Σ c) else ca Σ c'; ca_init := ca_init Σ; sec := sec Σ; sec_nres := sec_nres Σ;
      aw := aw Σ; ql := ql Σ; qg := qg Σ; dep := D'; fs0 := fs0 Σ; fsc0 := fsc0 Σ; fs4 := fs4 Σ; fs1 := fs1 Σ; fs3 := fs3 Σ; fs2 := fs2 Σ; ia_init := ia_init Σ; credit := credit Σ - mcost n;
      live := (p_ubeg SB c i n, n) :: live Σ; frames := frames Σ; ann := arem (p_ubeg SB c i n) (ann Σ) |} k) = fss_hint (fs_of Σ k)) as E by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; reflexivity).
    rewrite E. lia. }
  split.
  {
    unfold budget_wf. cbn [credit aw]. destruct W7 as (G1 & G2 & G3 & G4 & G5).
    assert (Hm0 : 0 <= mcost n) by (unfold mcost, DCOST; destruct (n <=? 64512); lia).
    split; [lia|]. split; [exact G2|]. split; [lia|].
    assert (E : rt_eager (mal_hit Σ c n D') = rt_eager Σ).
    { unfold rt_eager, mal_hit. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
      destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; reflexivity | reflexivity]. }
    unfold mal_hit in E. cbn [pr sec sec_nres] in E. rewrite E. split; [exact G4|]. unfold secsum in *. cbn [sec]. lia. }
  split; [exact HDok|]. split; [cbn [length]; rewrite Nat2Z.inj_succ; unfold Z.succ; exact POT'|]. split; [lia|]. split; [exact (proj1 HDinv)|].
  destruct W12 as (K1 & K2). split; [|exact K2].
  intros c' i' n' Hc' Hq. destruct (hit_nth_cases c' i' (CkQuar n') Hq) as [(_ & _ & X)|(X & _)]; [discriminate X | exact (K1 c' i' n' Hc' X)].
Qed.

End Hit.

End GWIN.
