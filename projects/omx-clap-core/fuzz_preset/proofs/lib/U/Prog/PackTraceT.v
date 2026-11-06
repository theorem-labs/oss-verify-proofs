From Stdlib Require Import ZArith List Bool Lia Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack AllocPackRoom Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjGrowUp PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes PackFit PackOwn PackReparse PackVec PackBand.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pt_bi_rng : forall k n, 0 <= pq_bi k n <= 1.
Proof. intros k n. unfold pq_bi. destruct (band n =? k); lia. Qed.

Lemma pt_bcnt_cons : forall a s k, po_bcnt (a :: s) k = pq_bi k (Z.of_nat a + 16) + po_bcnt s k.
Proof.
  intros a s k. unfold po_bcnt, pq_bi. cbn [filter].
  destruct (band (Z.of_nat a + 16) =? k); cbn [length]; lia.
Qed.

Lemma pt_bcnt_rm : forall m s k,
  po_bcnt s k <= po_bcnt (ReaderRes.rm1n m s) k + pq_bi k (Z.of_nat m + 16).
Proof.
  intros m s k. induction s as [|x s IH]; cbn [ReaderRes.rm1n].
  - pose proof (pt_bi_rng k (Z.of_nat m + 16)). unfold po_bcnt. cbn [filter length]. lia.
  - destruct (Nat.eqb_spec x m) as [->|Hne].
    + rewrite pt_bcnt_cons. lia.
    + rewrite !pt_bcnt_cons. lia.
Qed.

Lemma pt_lsz_ev : forall s e k, (forall m n, e = EGrow m n -> (m < n)%nat) ->
  pq_ev k e + po_bcnt s k <= po_bcnt (ReaderRes.lsz_ev s e) k.
Proof.
  intros s e k He. destruct e as [n|[|m] n|n|n]; cbn [pq_ev ReaderRes.lsz_ev Nat.eqb].
  - rewrite pt_bcnt_cons. lia.
  - rewrite pt_bcnt_cons. lia.
  - pose proof (He (S m) n eq_refl) as Hl.
    pose proof (band_mono (Z.of_nat (S m) + 16) (Z.of_nat n + 16) ltac:(lia)) as Hb.
    destruct (Z.ltb_spec (band (Z.of_nat n + 16)) (band (Z.of_nat (S m) + 16))) as [L|L]; [lia|].
    rewrite pt_bcnt_cons. pose proof (pt_bcnt_rm (S m) s k). lia.
  - lia.
  - pose proof (pt_bcnt_rm n s k). lia.
Qed.

Theorem pq_lsz : forall s tr k, grow_up tr ->
  pq_run k tr + po_bcnt s k <= po_bcnt (fold_left ReaderRes.lsz_ev tr s) k.
Proof.
  intros s tr k. revert s. induction tr as [|e tr IH]; intros s Hg; cbn [pq_run fold_left]; [lia|].
  assert (He : forall m n, e = EGrow m n -> (m < n)%nat) by (intros m n ->; apply (Hg m n); left; reflexivity).
  assert (Ht : grow_up tr) by (intros m n Hi; apply (Hg m n); right; exact Hi).
  pose proof (pt_lsz_ev s e k He). pose proof (IH (ReaderRes.lsz_ev s e) Ht). lia.
Qed.

Corollary pq_lsz0 : forall tr k, grow_up tr -> pq_run k tr <= po_bcnt (ReaderRes.lsz tr) k.
Proof.
  intros tr k Hg. pose proof (pq_lsz [] tr k Hg) as H. change (po_bcnt [] k) with 0 in H.
  unfold ReaderRes.lsz. lia.
Qed.

Lemma pt_nlive_calls : forall P, nlive P <= Z.of_nat (calls P).
Proof.
  induction P as [|e P IH]; cbn [nlive calls]; [lia|].
  destruct e as [n|[|m] n|n|n]; cbn [nlive_ev is_call]; lia.
Qed.

Theorem run_bytes : forall sm x ok P R, snd (jr_run sm x ok) = P ++ R ->
  held P + 16 * nlive P <= 256 * Z.of_nat (length x) + 16448.
Proof.
  intros sm x ok P R E.
  pose proof (G10 sm x ok P R E) as H1.
  pose proof (G7_4 sm x ok) as H2. rewrite E, calls_app in H2.
  pose proof (pt_nlive_calls P). lia.
Qed.

Definition pt_es (B : nat) (t : list ev) : Prop := Forall (fun e => is_call e = true -> (esize e <= B)%nat) t.

Lemma pt_es_nil : forall B, pt_es B [].
Proof. intros B. apply Forall_nil. Qed.

Lemma pt_es_mono : forall B B' t, (B <= B')%nat -> pt_es B t -> pt_es B' t.
Proof. intros B B' t Hb H. eapply Forall_impl; [|exact H]. intros e He Hc. specialize (He Hc). lia. Qed.

Lemma pt_es_app : forall B a b, pt_es B a -> pt_es B b -> pt_es B (a ++ b).
Proof. intros B a b Ha Hb. apply Forall_app. split; assumption. Qed.

Definition pt_sh (B : nat) (t : list ev) : Prop :=
  t = [] \/ exists a, (a <= B)%nat /\ (t = [EAlloc a] \/ t = [EFail a] \/ t = [EAlloc a; EFree a]).

Definition pt_sh0 (B : nat) (t : list ev) : Prop := t = [] \/ exists a, (a <= B)%nat /\ t = [EAlloc a].

Lemma pt_sh_nil : forall B, pt_sh B [].
Proof. intros B. left. reflexivity. Qed.

Lemma pt_sh_mono : forall B B' t, (B <= B')%nat -> pt_sh B t -> pt_sh B' t.
Proof. intros B B' t Hb [H|(a & Ha & H)]; [left; exact H|right; exists a; split; [lia|exact H]]. Qed.

Ltac pt_es_solve := unfold pt_es;
  repeat (apply Forall_cons; [intros ?; cbn [esize is_call] in *; first [discriminate | lia]|]); apply Forall_nil.

Ltac pt_shc := unfold pt_sh; first [left; reflexivity | right; eexists; split;
  [| first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]]; lia].

Lemma pt_sh_es : forall B t, pt_sh B t -> pt_es B t.
Proof. intros B t [->|(a & Ha & [->|[->| ->]])]; pt_es_solve. Qed.

Lemma pt_str_sh : forall z ok, pt_sh (length z) (snd (fst (jr_string z ok))).
Proof.
  intros z ok. unfold jr_string.
  destruct (scan z) as [q|] eqn:Es.
  - pose proof (scan_quote z q Es) as [Hq _].
    unfold jbind, jalloc, take.
    destruct ok as [|b ok]; [|destruct b]; cbv beta iota.
    + destruct (decode z) as [[s r]|]; cbv beta iota; unfold jret, jfree, jrefuse; cbn [fst snd app]; pt_shc.
    + destruct (decode z) as [[s r]|]; cbv beta iota; unfold jret, jfree, jrefuse; cbn [fst snd app]; pt_shc.
    + cbn [fst snd app]. pt_shc.
  - unfold jrefuse. cbn [fst snd]. apply pt_sh_nil.
Qed.

Lemma pt_name_sh : forall o y ok, pt_sh (length y) (snd (fst (jr_name o y ok))).
Proof.
  intros o y ok. unfold jr_name. destruct o.
  2: { unfold jret. cbn [fst snd]. apply pt_sh_nil. }
  destruct (skip y) as [|b z] eqn:Ey.
  { unfold jrefuse. cbn [fst snd]. apply pt_sh_nil. }
  pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
  destruct (b =? 34).
  2: { unfold jrefuse. cbn [fst snd]. apply pt_sh_nil. }
  unfold jbind at 1. pose proof (pt_str_sh z ok) as Hs. pose proof (jr_string_spec z ok) as Hp.
  destruct (jr_string z ok) as [[[[nm r]|] t] ok1] eqn:Ej; cbn [fst snd] in Hs.
  - destruct Hp as (q & Hsc & _ & -> & Hl).
    assert (Hb : sblock z = S q) by (unfold sblock; rewrite Hsc; reflexivity).
    cbv beta iota.
    destruct (skip r) as [|c r1]; [|destruct (c =? 58)]; cbv beta iota;
      unfold jbind, jfree, jret, jrefuse; rewrite ?Hb; cbn [fst snd app]; pt_shc.
  - cbn [fst snd]. eapply pt_sh_mono; [|exact Hs]. lia.
Qed.

Lemma pt_lit_nil : forall w v x ok, w <> [] -> snd (fst (lit w v x ok)) = [].
Proof.
  intros w v x ok Hw. pose proof (lit_spec w v x ok Hw) as H.
  destruct (lit w v x ok) as [[[[u r]|] t] ok']; cbn [fst snd]; [destruct H as [H _]|]; exact H.
Qed.

Lemma pt_name_some : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  pt_sh0 (length y) tn /\ (length y1 <= length y)%nat.
Proof.
  intros o y ok nm y1 tn ok2 H. pose proof (jr_name_spec o y ok) as S. rewrite H in S.
  destruct o.
  - destruct S as (q & -> & Hq). split; [right; exists (S q); split; [lia|reflexivity]|lia].
  - destruct S as [-> ->]. split; [left; reflexivity|lia].
Qed.

Lemma pt_grow_es : forall o n cap ok, pt_es (112 * n + 448) (snd (fst (grow o n cap ok))).
Proof.
  intros o n cap ok. unfold grow.
  destruct (Nat.ltb n cap) eqn:E.
  - unfold jret. cbn [fst snd]. apply pt_es_nil.
  - apply Nat.ltb_ge in E. cbv zeta.
    destruct (Nat.eqb cap 0) eqn:Ec;
      [assert (Hc : (56 * 8 <= 112 * n + 448)%nat) by lia
      |assert (Hc : (56 * (2 * cap) <= 112 * n + 448)%nat) by lia];
      unfold jbind, jrealloc, take, jret;
      (destruct ok as [|b1 ok]; [|destruct b1]; cbv beta iota;
       [destruct o; cbv beta iota; cbn [fst snd app]; pt_es_solve
       |destruct o; cbv beta iota; [destruct ok as [|b2 ok]; [|destruct b2]; cbv beta iota|];
          cbn [fst snd app]; pt_es_solve
       |cbn [fst snd app]; pt_es_solve]).
Qed.

Section Es.

Variable sm : list Z -> Z * Z.

Lemma pt_num_sh : forall x ok, pt_sh (S (length x)) (snd (fst (jr_number sm x ok))).
Proof.
  intros x ok. unfold jr_number. cbv zeta.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end).
  assert (Hj : (j <= length x)%nat).
  { unfold j. destruct x as [|b x']; [cbn; lia|]. destruct (b =? 45); cbn [length]; lia. }
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c z] eqn:Ez.
  { unfold jrefuse. cbn [fst snd]. apply pt_sh_nil. }
  destruct (negb (digit c)).
  { unfold jrefuse. cbn [fst snd]. apply pt_sh_nil. }
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end).
  { unfold jrefuse. cbn [fst snd]. apply pt_sh_nil. }
  destruct (span numch z) as [a r] eqn:Es.
  pose proof (span_app _ _ _ _ Es) as Hz.
  assert (Ht : (length (firstn j x ++ c :: a) <= length x)%nat).
  { rewrite length_app, length_firstn. cbn [length]. cbn [length] in Hsk. rewrite Hz, length_app in Hsk. lia. }
  unfold jbind, jalloc, take.
  destruct ok as [|bb ok]; [|destruct bb]; cbv beta iota.
  - destruct (whole sm (firstn j x ++ c :: a)); unfold jret, jrefuse; cbn [fst snd app]; pt_shc.
  - destruct (whole sm (firstn j x ++ c :: a)); unfold jret, jrefuse; cbn [fst snd app]; pt_shc.
  - cbn [fst snd]. pt_shc.
Qed.

Lemma pt_cont_es : forall f d o b y ok,
  (forall o' n cap acc y' ok',
     pt_es (56 * length y' + 112 * n + 504) (snd (fst (jrl sm f (S d) o' n cap acc y' ok')))) ->
  pt_es (56 * length (b :: y) + 448) (snd (fst (jr_cont (jrl sm f) d o (b :: y) ok))).
Proof.
  intros f d o b y ok HL. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)).
  - unfold jrefuse. cbn [fst snd]. apply pt_es_nil.
  - cbn [tl]. pose proof (skip_len y) as Hy.
    assert (K : forall y', (length y' <= length y)%nat ->
      pt_es (56 * length (b :: y) + 448) (snd (fst (jrl sm f (S d) o 0 0 [] y' ok)))).
    { intros y' Hl. eapply pt_es_mono; [|apply HL]. cbn [length]. lia. }
    destruct (skip y) as [|c r] eqn:Ey; [apply K; cbn [length]; lia|].
    destruct (c =? closer o); [|apply K; exact Hy].
    unfold jret. cbn [fst snd]. apply pt_es_nil.
Qed.

Lemma pt_es_fuel : forall f,
  (forall d x ok, pt_es (56 * length x + 448) (snd (fst (jrv sm f d x ok)))) /\
  (forall d o n cap acc y ok,
     pt_es (56 * length y + 112 * n + 504) (snd (fst (jrl sm f d o n cap acc y ok)))).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl]; unfold jrefuse; cbn [fst snd]; apply pt_es_nil.
  - split.
    + intros d x ok. cbn [jrv]. pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex.
      { unfold jrefuse. cbn [fst snd]. apply pt_es_nil. }
      cbn [length] in Hsx.
      assert (Hc : forall o, pt_es (56 * length x + 448) (snd (fst (jr_cont (jrl sm f) d o (b :: y) ok)))).
      { intros o. eapply pt_es_mono; [|apply pt_cont_es; intros; apply IHl]. cbn [length]. lia. }
      destruct (b =? 123); [apply Hc|].
      destruct (b =? 91); [apply Hc|].
      destruct (b =? 34).
      { unfold jbind. pose proof (pt_str_sh y ok) as Hs.
        destruct (jr_string y ok) as [[[[s r]|] t] ok1] eqn:Ej; cbn [fst snd] in Hs.
        - cbv beta iota. unfold jret. cbn [fst snd]. rewrite app_nil_r.
          eapply pt_es_mono; [|apply pt_sh_es; exact Hs]. lia.
        - cbn [fst snd]. eapply pt_es_mono; [|apply pt_sh_es; exact Hs]. lia. }
      destruct (b =? 116); [rewrite pt_lit_nil by discriminate; apply pt_es_nil|].
      destruct (b =? 102); [rewrite pt_lit_nil by discriminate; apply pt_es_nil|].
      destruct (b =? 110); [rewrite pt_lit_nil by discriminate; apply pt_es_nil|].
      eapply pt_es_mono; [|apply pt_sh_es, pt_num_sh]. cbn [length]. lia.
    + intros d o n cap acc y ok. cbn [jrl]. unfold jbind at 1.
      pose proof (pt_grow_es o n cap ok) as HG.
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1] eqn:Eg; cbn [fst snd] in HG.
      2: { cbn [fst snd]. eapply pt_es_mono; [|exact HG]. lia. }
      assert (HG' : pt_es (56 * length y + 112 * n + 504) tg) by (eapply pt_es_mono; [|exact HG]; lia).
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (pt_name_sh o y ok1) as HN.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2] eqn:En; cbn [fst snd] in HN;
        assert (HN' : pt_es (56 * length y + 112 * n + 504) tn)
          by (eapply pt_es_mono; [|apply pt_sh_es; exact HN]; lia).
      2: { cbn [fst snd]. apply pt_es_app; assumption. }
      destruct (pt_name_some o y ok1 nm y1 tn ok2 En) as [_ Hy1].
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (IHv d y1 ok2) as HV. pose proof (proj1 (spec_fuel sm f) d y1 ok2) as SV.
      destruct (jrv sm f d y1 ok2) as [[[[v r]|] tv] ok3] eqn:Ev; cbn [fst snd] in HV;
        assert (HV' : pt_es (56 * length y + 112 * n + 504) tv) by (eapply pt_es_mono; [|exact HV]; lia).
      2: { cbn [fst snd]. apply pt_es_app; [assumption|]. apply pt_es_app; assumption. }
      unfold vspec in SV. cbn [fst snd] in SV. destruct SV as (_ & _ & SV).
      destruct (SV v r eq_refl) as (Hr & _ & _).
      cbv beta iota. pose proof (skip_len r) as Hsr.
      destruct (skip r) as [|c r1] eqn:Er.
      { cbv beta iota. unfold jrefuse. cbn [fst snd]. rewrite app_nil_r.
        apply pt_es_app; [assumption|]. apply pt_es_app; assumption. }
      cbn [length] in Hsr.
      destruct (c =? 44); cbv beta iota.
      { pose proof (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3) as HR.
        destruct (jrl sm f d o (S n) cap1 ((nm, v) :: acc) r1 ok3) as [[res t'] ok4] eqn:El.
        cbn [fst snd] in HR |- *. apply pt_es_app; [assumption|]. apply pt_es_app; [assumption|].
        apply pt_es_app; [assumption|]. eapply pt_es_mono; [|exact HR]. lia. }
      destruct (c =? closer o); cbv beta iota.
      { unfold jret. cbn [fst snd]. rewrite app_nil_r. apply pt_es_app; [assumption|]. apply pt_es_app; assumption. }
      { unfold jrefuse. cbn [fst snd]. rewrite app_nil_r. apply pt_es_app; [assumption|]. apply pt_es_app; assumption. }
Qed.

End Es.

Theorem run_esize : forall sm x ok e, In e (snd (jr_run sm x ok)) -> is_call e = true ->
  Z.of_nat (esize e) <= 56 * Z.of_nat (length x) + 448.
Proof.
  intros sm x ok e Hi Hc. rewrite jr_run_eq in Hi. cbn [snd] in Hi.
  pose proof (proj1 (pt_es_fuel sm (S (2 * length x))) 0%nat x ok) as H.
  unfold pt_es in H. rewrite Forall_forall in H. specialize (H e Hi Hc). lia.
Qed.

Ltac pt_bit := repeat match goal with
  | |- context [pq_bi ?kk ?nn] =>
      lazymatch goal with _ : 0 <= pq_bi kk nn <= 1 |- _ => fail | _ => pose proof (pt_bi_rng kk nn) end
  | _ : context [pq_bi ?kk ?nn] |- _ =>
      lazymatch goal with _ : 0 <= pq_bi kk nn <= 1 |- _ => fail | _ => pose proof (pt_bi_rng kk nn) end
  end.

Ltac pt_eqbt := repeat match goal with
  | |- context [Nat.eqb ?a 0] => destruct (Nat.eqb_spec a 0); cbv beta iota; try (exfalso; lia)
  end.

Lemma pt_gcap_ge : forall n cap, (cap <= gcap n cap)%nat.
Proof. intros n cap. unfold gcap. destruct (Nat.ltb n cap); [lia|]. destruct (Nat.eqb_spec cap 0); lia. Qed.

Lemma pt_pq_app : forall k a b, pq_run k (a ++ b) = pq_run k a + pq_run k b.
Proof. intros k. induction a as [|e a IH]; intros b; cbn [app pq_run]; [lia|]. rewrite IH. lia. Qed.

Section Pq.

Variable sm : list Z -> Z * Z.
Variable k : Z.

Definition pt_suf (c : Z) (t : list ev) : Prop := forall P R, t = P ++ R -> - c <= pq_run k R.

Lemma pt_suf_nil : forall c, 0 <= c -> pt_suf c [].
Proof. intros c Hc P R H. symmetry in H. apply app_eq_nil in H as [_ ->]. cbn [pq_run]. lia. Qed.

Lemma pt_suf_cons : forall c e t, pt_suf c t -> - c <= pq_ev k e + pq_run k t -> pt_suf c (e :: t).
Proof.
  intros c e t Ht He P R H. destruct P as [|e' P].
  - cbn [app] in H. subst R. cbn [pq_run]. exact He.
  - cbn [app] in H. injection H as _ H. exact (Ht P R H).
Qed.

Lemma pt_suf_mono : forall c c' t, c <= c' -> pt_suf c t -> pt_suf c' t.
Proof. intros c c' t Hc H P R E. specialize (H P R E). lia. Qed.

Lemma pt_suf_app : forall ca cb c a b, pt_suf ca a -> pt_suf cb b -> ca - pq_run k b <= c -> cb <= c ->
  pt_suf c (a ++ b).
Proof.
  intros ca cb c a b Ha Hb H1 H2 P R E.
  destruct (app_eq_app a b P R E) as (l & [[E1 E2]|[E1 E2]]).
  - subst R. rewrite pt_pq_app. pose proof (Ha P l E1). lia.
  - pose proof (Hb l R E2). lia.
Qed.

Definition pt_phi (o : bool) (cap : nat) : Z :=
  if Nat.eqb cap 0 then 0
  else pq_bi k (Z.of_nat (56 * cap) + 16) + (if o then pq_bi k (Z.of_nat (8 * cap) + 16) else 0).

Lemma pt_phi_rng : forall o cap, 0 <= pt_phi o cap <= 2.
Proof.
  intros o cap. unfold pt_phi. destruct (Nat.eqb cap 0); [lia|].
  pose proof (pt_bi_rng k (Z.of_nat (56 * cap) + 16)). pose proof (pt_bi_rng k (Z.of_nat (8 * cap) + 16)).
  destruct o; lia.
Qed.

Lemma pt_grow_ev : forall m n, (m <= n)%nat ->
  pq_ev k (EGrow m n) = pq_bi k (Z.of_nat n + 16) - (if Nat.eqb m 0 then 0 else pq_bi k (Z.of_nat m + 16)).
Proof.
  intros m n Hmn. cbn [pq_ev]. destruct (Nat.eqb m 0); [lia|].
  pose proof (band_mono (Z.of_nat m + 16) (Z.of_nat n + 16) ltac:(lia)).
  destruct (Z.ltb_spec (band (Z.of_nat n + 16)) (band (Z.of_nat m + 16))); lia.
Qed.

Lemma pt_grow_some : forall o n cap,
  pq_run k (grow_ev o n cap) + pt_phi o cap = pt_phi o (gcap n cap) /\
  pt_suf (2 - pt_phi o (gcap n cap)) (grow_ev o n cap).
Proof.
  intros o n cap. pose proof (pt_phi_rng o cap) as P0. unfold grow_ev, gcap.
  destruct (Nat.ltb n cap).
  - cbn [pq_run]. split; [lia|]. apply pt_suf_nil. lia.
  - assert (Hc : (cap <= (if Nat.eqb cap 0 then 8 else 2 * cap))%nat /\
                 (if Nat.eqb cap 0 then 8 else 2 * cap)%nat <> 0%nat) by (destruct (Nat.eqb_spec cap 0); lia).
    revert Hc. generalize (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat). intros c' [H1 H2].
    destruct o; cbn [pq_run]; rewrite ?pt_grow_ev by lia; (split;
      [unfold pt_phi; cbv beta iota; pt_eqbt; pt_bit; lia
      |repeat (apply pt_suf_cons;
                 [|cbn [pq_run]; rewrite ?pt_grow_ev by lia; unfold pt_phi; cbv beta iota; pt_eqbt; pt_bit; lia]);
       apply pt_suf_nil; unfold pt_phi; cbv beta iota; pt_eqbt; pt_bit; lia]).
Qed.

Lemma pt_grow_none : forall o n cap ok tg ok', grow o n cap ok = (None, tg, ok') ->
  0 <= pq_run k tg + pt_phi o cap /\ pt_suf 2 tg.
Proof.
  intros o n cap ok tg ok' H. pose proof (pt_phi_rng o cap) as P0. pose proof (pt_gcap_ge n cap) as Hg.
  destruct (po_grow_none o n cap ok tg ok' H) as [-> | [-> ->]].
  - cbn [pq_run pq_ev]. split; [lia|].
    apply pt_suf_cons; [apply pt_suf_nil; lia|]. cbn [pq_run pq_ev]. lia.
  - cbn [pq_run]. rewrite pt_grow_ev by lia. cbn [pq_ev]. split.
    + unfold pt_phi; cbv beta iota; pt_eqbt; pt_bit; lia.
    + apply pt_suf_cons; [apply pt_suf_cons; [apply pt_suf_nil; lia|]|];
        cbn [pq_run]; rewrite ?pt_grow_ev by lia; cbn [pq_ev]; pt_eqbt; pt_bit; lia.
Qed.

Lemma pt_sh_pq : forall B t, pt_sh B t -> 0 <= pq_run k t /\ pt_suf 1 t.
Proof.
  intros B t [->|(a & _ & [->|[->| ->]])]; cbn [pq_run pq_ev]; pt_bit; (split; [lia|]);
    repeat (apply pt_suf_cons; [|cbn [pq_run pq_ev]; pt_bit; lia]); apply pt_suf_nil; lia.
Qed.

Lemma pt_sh0_pq : forall B t, pt_sh0 B t -> 0 <= pq_run k t /\ pt_suf 0 t.
Proof.
  intros B t [->|(a & _ & ->)]; cbn [pq_run pq_ev]; pt_bit; (split; [lia|]).
  - apply pt_suf_nil; lia.
  - apply pt_suf_cons; [apply pt_suf_nil; lia|]. cbn [pq_run pq_ev]. pt_bit. lia.
Qed.

Definition pt_vok (d : nat) (t : list ev) : Prop :=
  0 <= pq_run k t /\ pt_suf (2 * Z.of_nat (MAXD - d) + 1) t.

Definition pt_lok (d : nat) (o : bool) (cap : nat) (t : list ev) : Prop :=
  0 <= pq_run k t + pt_phi o cap /\ pt_suf (2 * Z.of_nat (MAXD - d) + 3) t.

Lemma pt_vok_sh : forall d B t, pt_sh B t -> pt_vok d t.
Proof.
  intros d B t H. destruct (pt_sh_pq B t H) as [A S]. split; [exact A|]. eapply pt_suf_mono; [|exact S]. lia.
Qed.

Lemma pt_lok_comb : forall d o cap cap1 tg tn tv tr,
  pq_run k tg + pt_phi o cap = pt_phi o cap1 -> pt_suf (2 - pt_phi o cap1) tg ->
  0 <= pq_run k tn -> pt_suf 0 tn -> pt_vok d tv ->
  0 <= pq_run k tr + pt_phi o cap1 -> pt_suf (2 * Z.of_nat (MAXD - d) + 3) tr ->
  pt_lok d o cap (tg ++ tn ++ tv ++ tr).
Proof.
  intros d o cap cap1 tg tn tv tr G1 G2 N1 N2 [V1 V2] R1 R2.
  pose proof (pt_phi_rng o cap1) as P1.
  split.
  - rewrite !pt_pq_app. lia.
  - apply (pt_suf_app (2 - pt_phi o cap1) (2 * Z.of_nat (MAXD - d) + 3)); [exact G2| | |lia].
    + apply (pt_suf_app 0 (2 * Z.of_nat (MAXD - d) + 3)); [exact N2| | |lia].
      * apply (pt_suf_app (2 * Z.of_nat (MAXD - d) + 1) (2 * Z.of_nat (MAXD - d) + 3)); [exact V2|exact R2|lia|lia].
      * rewrite !pt_pq_app. lia.
    + rewrite !pt_pq_app. lia.
Qed.

Lemma pt_lok_nil : forall d o cap cap1 tg tn tv,
  pq_run k tg + pt_phi o cap = pt_phi o cap1 -> pt_suf (2 - pt_phi o cap1) tg ->
  0 <= pq_run k tn -> pt_suf 0 tn -> pt_vok d tv ->
  pt_lok d o cap (tg ++ tn ++ tv ++ []).
Proof.
  intros d o cap cap1 tg tn tv G1 G2 N1 N2 V.
  pose proof (pt_phi_rng o cap1) as P1.
  apply (pt_lok_comb d o cap cap1); try assumption; [cbn [pq_run]; lia|apply pt_suf_nil; lia].
Qed.

Lemma pt_lok_nf : forall d o cap cap1 tg tn,
  pq_run k tg + pt_phi o cap = pt_phi o cap1 -> pt_suf (2 - pt_phi o cap1) tg ->
  0 <= pq_run k tn -> pt_suf 1 tn -> pt_lok d o cap (tg ++ tn).
Proof.
  intros d o cap cap1 tg tn G1 G2 N1 N2. pose proof (pt_phi_rng o cap1).
  split; [rewrite pt_pq_app; lia|].
  apply (pt_suf_app (2 - pt_phi o cap1) 1); [exact G2|exact N2|lia|lia].
Qed.

Lemma pt_cont : forall f d o b y ok,
  (forall o' n cap acc y' ok', pt_lok (S d) o' cap (snd (fst (jrl sm f (S d) o' n cap acc y' ok')))) ->
  pt_vok d (snd (fst (jr_cont (jrl sm f) d o (b :: y) ok))).
Proof.
  intros f d o b y ok HL. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed.
  - unfold jrefuse. cbn [fst snd]. apply (pt_vok_sh d 0). apply pt_sh_nil.
  - apply Nat.ltb_ge in Ed. cbn [tl].
    assert (K : forall y', pt_vok d (snd (fst (jrl sm f (S d) o 0 0 [] y' ok)))).
    { intros y'. destruct (HL o 0%nat 0%nat [] y' ok) as [A B]. split.
      - change (pt_phi o 0) with 0 in A. lia.
      - eapply pt_suf_mono; [|exact B]. lia. }
    destruct (skip y) as [|c r] eqn:Ey; [apply K|].
    destruct (c =? closer o); [|apply K].
    unfold jret. cbn [fst snd]. apply (pt_vok_sh d 0). apply pt_sh_nil.
Qed.

Lemma pt_fuel : forall f,
  (forall d x ok, pt_vok d (snd (fst (jrv sm f d x ok)))) /\
  (forall d o n cap acc y ok, pt_lok d o cap (snd (fst (jrl sm f d o n cap acc y ok)))).
Proof.
  induction f as [|f [IHv IHl]].
  - split.
    + intros d x ok. cbn [jrv]. unfold jrefuse. cbn [fst snd]. apply (pt_vok_sh d 0). apply pt_sh_nil.
    + intros d o n cap acc y ok. cbn [jrl]. unfold jrefuse. cbn [fst snd]. pose proof (pt_phi_rng o cap).
      split; [cbn [pq_run]; lia|apply pt_suf_nil; lia].
  - split.
    + intros d x ok. cbn [jrv].
      destruct (skip x) as [|b y] eqn:Ex.
      { unfold jrefuse. cbn [fst snd]. apply (pt_vok_sh d 0). apply pt_sh_nil. }
      destruct (b =? 123); [apply pt_cont; intros; apply IHl|].
      destruct (b =? 91); [apply pt_cont; intros; apply IHl|].
      destruct (b =? 34).
      { unfold jbind. pose proof (pt_str_sh y ok) as Hs. pose proof (jr_string_spec y ok) as Hp.
        destruct (jr_string y ok) as [[[[s r]|] t] ok1] eqn:Ej; cbn [fst snd] in Hs.
        - destruct Hp as (q & _ & _ & -> & _). cbv beta iota. unfold jret. cbn [fst snd app].
          apply (pt_vok_sh d (S q)). pt_shc.
        - cbn [fst snd]. exact (pt_vok_sh d _ _ Hs). }
      destruct (b =? 116); [rewrite pt_lit_nil by discriminate; apply (pt_vok_sh d 0); apply pt_sh_nil|].
      destruct (b =? 102); [rewrite pt_lit_nil by discriminate; apply (pt_vok_sh d 0); apply pt_sh_nil|].
      destruct (b =? 110); [rewrite pt_lit_nil by discriminate; apply (pt_vok_sh d 0); apply pt_sh_nil|].
      exact (pt_vok_sh d _ _ (pt_num_sh sm (b :: y) ok)).
    + intros d o n cap acc y ok. cbn [jrl]. unfold jbind at 1.
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1] eqn:Eg.
      2: { cbn [fst snd]. destruct (pt_grow_none o n cap ok tg ok1 Eg) as [A B].
           split; [exact A|]. eapply pt_suf_mono; [|exact B]. lia. }
      destruct (grow_ok o n cap ok cap1 tg ok1 Eg) as [-> ->].
      destruct (pt_grow_some o n cap) as [G1 G2].
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (pt_name_sh o y ok1) as Hn.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2] eqn:En; cbn [fst snd] in Hn.
      2: { cbn [fst snd]. destruct (pt_sh_pq _ _ Hn) as [N1 N2]. exact (pt_lok_nf d o cap _ _ _ G1 G2 N1 N2). }
      destruct (pt_name_some o y ok1 nm y1 tn ok2 En) as [Hn0 _].
      destruct (pt_sh0_pq _ _ Hn0) as [N1 N2].
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (IHv d y1 ok2) as HV.
      destruct (jrv sm f d y1 ok2) as [[[[v r]|] tv] ok3] eqn:Ev; cbn [fst snd] in HV.
      2: { cbn [fst snd]. rewrite <- (app_nil_r tv). exact (pt_lok_nil d o cap _ _ _ _ G1 G2 N1 N2 HV). }
      cbv beta iota.
      destruct (skip r) as [|c r1] eqn:Er.
      { cbv beta iota. unfold jrefuse. cbn [fst snd]. exact (pt_lok_nil d o cap _ _ _ _ G1 G2 N1 N2 HV). }
      destruct (c =? 44); cbv beta iota.
      { pose proof (IHl d o (S n) (gcap n cap) ((nm, v) :: acc) r1 ok3) as HR.
        destruct (jrl sm f d o (S n) (gcap n cap) ((nm, v) :: acc) r1 ok3) as [[res t'] ok4] eqn:El.
        cbn [fst snd] in HR |- *. destruct HR as [R1 R2].
        exact (pt_lok_comb d o cap _ _ _ _ _ G1 G2 N1 N2 HV R1 R2). }
      destruct (c =? closer o); cbv beta iota.
      { unfold jret. cbn [fst snd]. exact (pt_lok_nil d o cap _ _ _ _ G1 G2 N1 N2 HV). }
      { unfold jrefuse. cbn [fst snd]. exact (pt_lok_nil d o cap _ _ _ _ G1 G2 N1 N2 HV). }
Qed.

End Pq.

Theorem run_prefix_65 : forall sm x ok P R, snd (jr_run sm x ok) = P ++ R ->
  forall k, pq_run k P <= pq_run k (snd (jr_run sm x ok)) + 65.
Proof.
  intros sm x ok P R E k.
  pose proof (proj1 (pt_fuel sm k (S (2 * length x))) 0%nat x ok) as [_ H].
  rewrite jr_run_eq in E |- *. cbn [snd] in E |- *.
  specialize (H P R E). rewrite E, pt_pq_app.
  change (Z.of_nat (MAXD - 0)) with 32 in H. lia.
Qed.

Theorem run_prefix : forall sm x ok P R, snd (jr_run sm x ok) = P ++ R ->
  forall k, pq_run k P <= pq_run k (snd (jr_run sm x ok)) + 100.
Proof.
  intros sm x ok P R E k. pose proof (run_prefix_65 sm x ok P R E k). lia.
Qed.

Ltac pt_perm := rewrite ?app_nil_r; apply (proj2 (@Permutation_count_occ nat Nat.eq_dec _ _)); intros ?;
  rewrite ?count_occ_app; cbn [count_occ]; lia.

Definition pt_cbs (L : list (list Z * jv)) : list nat := flat_map (fun m => pq_cb (snd m)) L.

Lemma pt_cb_mk : forall o L, pq_cb (mk o L) = rkb o (rfcap (length L) 0 0) ++ pt_cbs L.
Proof.
  intros [|] L; cbn [mk pq_cb]; unfold pt_cbs.
  - f_equal. apply flat_map_ext. intros [a u]. reflexivity.
  - rewrite length_map. f_equal. induction L as [|m L IH]; [reflexivity|]. cbn [map flat_map]. rewrite IH. reflexivity.
Qed.

Section Cb.

Variable sm : list Z -> Z * Z.

Definition pt_cv (f : nat) : Prop :=
  forall d x ok t r tr ok', jrv sm f d x ok = (Some (t, r), tr, ok') ->
    exists I, forall s, Permutation (fold_left ReaderRes.lsz_ev tr s) (pq_cb t ++ I ++ s).

Definition pt_cl (f : nat) : Prop :=
  forall d o n cap acc y ok t r tr ok', jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') ->
    exists L I, t = mk o (rev acc ++ L) /\
      (forall s s0, Permutation s (rkb o cap ++ s0) ->
         Permutation (fold_left ReaderRes.lsz_ev tr s) (rkb o (rfcap (length L) n cap) ++ pt_cbs L ++ I ++ s0)).

Lemma pt_cont_cb : forall f d o b y ok t r tr ok', pt_cl f ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (t, r), tr, ok') ->
  exists I, forall s, Permutation (fold_left ReaderRes.lsz_ev tr s) (pq_cb t ++ I ++ s).
Proof.
  intros f d o b y ok t r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H.
  assert (K : forall y' ok0, jrl sm f (S d) o 0 0 [] y' ok0 = (Some (t, r), tr, ok') ->
     exists I, forall s, Permutation (fold_left ReaderRes.lsz_ev tr s) (pq_cb t ++ I ++ s)).
  { intros y' ok0 E. destruct (IHl _ _ _ _ _ _ _ _ _ _ _ E) as (L & I & -> & P).
    exists I. intros s. cbn [rev app]. rewrite pt_cb_mk, <- !app_assoc.
    apply P. apply Permutation_refl. }
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H.
  - exact (K _ _ H).
  - destruct (c =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as <- <- <- _. exists []. intros s. destruct o; cbn; apply Permutation_refl.
    + exact (K _ _ H).
Qed.

Lemma pt_cb_fuel : forall f, pt_cv f /\ pt_cl f.
Proof.
  induction f as [|f [IHv IHl]].
  - split; [intros d x ok t r tr ok' H|intros d o n cap acc y ok t r tr ok' H];
      cbn [jrv jrl] in H; unfold jrefuse in H; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (b =? 123); cbv beta iota in H; [exact (pt_cont_cb f d true b y ok t r tr ok' IHl H)|].
      destruct (b =? 91); cbv beta iota in H; [exact (pt_cont_cb f d false b y ok t r tr ok' IHl H)|].
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & Ht).
        destruct (jr_string_esc y ok s r1 t1 ok1 Hj) as (q & Ht1 & _ & _ & _).
        cbv beta iota in H. unfold jret in H. injection H as <- <- Ht2 _.
        exists [S q]. intros s'. subst tr t1 t2. apply Permutation_refl. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (lit_blk w_true JTrue _ _ _ _ _ _ ltac:(unfold w_true; discriminate) H) as [-> ->].
        exists []. intros s. apply Permutation_refl. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (lit_blk w_false JFalse _ _ _ _ _ _ ltac:(unfold w_false; discriminate) H) as [-> ->].
        exists []. intros s. apply Permutation_refl. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (lit_blk w_null JNull _ _ _ _ _ _ ltac:(unfold w_null; discriminate) H) as [-> ->].
        exists []. intros s. apply Permutation_refl. }
      destruct (jr_number_txt sm (b :: y) ok t r tr ok' H) as (txt & bits & -> & -> & _).
      exists [S (length txt)]. intros s. apply Permutation_refl.
    + intros d o n cap acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & Eg & H & Ht2). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & Ht3). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & Ht4). cbv beta iota in H.
      destruct (grow_ok o n cap ok cap1 tg ok1 Eg) as [-> ->].
      destruct (name_blk o y ok1 nm y1 tn ok2 En) as (nb & Fn & _).
      destruct (IHv d y1 ok2 v r0 tv ok3 Ev) as (Iv & Pv).
      assert (Pre : forall s s0, Permutation s (rkb o cap ++ s0) ->
                Permutation (fold_left ReaderRes.lsz_ev tv
                               (fold_left ReaderRes.lsz_ev tn (fold_left ReaderRes.lsz_ev (grow_ev o n cap) s)))
                  (rkb o (gcap n cap) ++ pq_cb v ++ (nb ++ Iv) ++ s0)).
      { intros s s0 Hs. rewrite Fn.
        pose proof (grow_perm o n cap s s0 Hs) as G.
        eapply Permutation_trans; [apply Pv|].
        eapply Permutation_trans; [apply Permutation_app_head, Permutation_app_head, Permutation_app_head, G|].
        pt_perm. }
      subst tr t2 t3.
      destruct (skip r0) as [|c r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (c =? 44); cbv beta iota in H.
      { destruct (IHl d o (S n) (gcap n cap) ((nm, v) :: acc) r1 ok3 t r t4 ok' H) as (L & I & -> & P).
        exists ((nm, v) :: L), (I ++ nb ++ Iv). split.
        - cbn [rev]. rewrite <- app_assoc. reflexivity.
        - intros s s0 Hs. rewrite !fold_left_app.
          eapply Permutation_trans; [apply P, Pre, Hs|].
          unfold pt_cbs. cbn [length rfcap flat_map snd]. pt_perm. }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as <- <- Ht _. subst t4.
      exists [(nm, v)], (nb ++ Iv). split.
      * reflexivity.
      * intros s s0 Hs. rewrite !fold_left_app. cbn [fold_left].
        eapply Permutation_trans; [apply Pre, Hs|]. unfold pt_cbs. cbn [length rfcap flat_map snd]. pt_perm.
Qed.

End Cb.

Theorem run_cb : forall sm x t, json_read sm x = Some t ->
  exists I, Permutation (ReaderRes.lsz (snd (jr_run sm x []))) (pq_cb t ++ I).
Proof.
  intros sm x t H. rewrite jr_run_eq. cbn [snd].
  unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  cbn [fst snd]. unfold jr_value in E.
  destruct (proj1 (pt_cb_fuel sm _) 0%nat x [] t' r tr ok' E) as (I & P).
  exists I. unfold ReaderRes.lsz. pose proof (P []) as P0. rewrite app_nil_r in P0. exact P0.
Qed.
