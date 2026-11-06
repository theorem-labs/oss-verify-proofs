(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnInv BnSpecs
  BgState BgWords BgLib BgArith BgMont BgExp BgInv BgSpecs BgFrame BgLibSpec BgDivSpec BgNumTheory.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma window_scan_ext : forall (f g : Z -> bool) wstart cnt i wv we,
  (forall n, 0 <= n -> f n = g n) -> window_scan f wstart cnt i wv we = window_scan g wstart cnt i wv we.
Proof.
  intros f g wstart cnt. induction cnt as [|c IH]; intros i wv we H; cbn [window_scan]; [reflexivity|].
  destruct (Z.ltb_spec (wstart - i) 0) as [Hl|Hge]; [reflexivity|]. rewrite H by lia.
  destruct (g (wstart - i)); apply IH; exact H.
Qed.

Lemma pow_sqr_step : forall x c, 0 <= c -> (x * x) ^ (2 ^ c) = x ^ (2 ^ (c + 1)).
Proof.
  intros x c Hc. rewrite Z.pow_add_r, Z.pow_1_r by lia. rewrite (Z.mul_comm (2 ^ c) 2), Z.pow_mul_r by (try apply Z.pow_nonneg; lia).
  f_equal. rewrite Z.pow_2_r. reflexivity.
Qed.

Lemma pow_window_step : forall a e k w, 0 <= a -> 0 <= e -> 0 <= k -> 0 <= w ->
  (a ^ e) ^ (2 ^ k) * a ^ w = a ^ (e * 2 ^ k + w).
Proof.
  intros a e k w Ha He Hk Hw. rewrite Z.pow_add_r by (try apply Z.mul_nonneg_nonneg; try apply Z.pow_nonneg; lia).
  rewrite Z.pow_mul_r by (try apply Z.pow_nonneg; lia). reflexivity.
Qed.

Section ExpLoops.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation BMu := (BM (M:=btree ptr) (ptr:=ptr)) (only parsing).

Record exp_kit : Type := mkKit {
  ek_mulop : bnref -> bnref -> bnref -> BMu unit;
  ek_Inv : ST -> Prop;
  ek_Rep : Z -> BN -> Prop;
  ek_rfree : bnref -> Prop;
  ek_wr : list bnref;
  ek_Fr : nat -> list bnref -> ST -> ST -> Prop;
  ek_D : nat;
  ek_P : nat;
  ek_Fr_refl : forall u o s, ek_Fr u o s s;
  ek_Fr_trans : forall u o1 o2 s s1 s2, ek_Fr u o1 s s1 -> ek_Fr u o2 s1 s2 -> ek_Fr u (o1 ++ o2) s s2;
  ek_Fr_weaken : forall u u' o o' s s',
    (u' <= u)%nat -> (forall r, In r o -> (r < NFIX + u')%nat -> In r o') -> ek_Fr u o s s' -> ek_Fr u' o' s s';
  ek_Fr_slot : forall u o s s' r, ek_Fr u o s s' -> (r < NFIX + u)%nat -> ~ In r o -> ~ In r ek_wr -> getbn r s' = getbn r s;
  ek_Fr_len : forall u o s s', ek_Fr u o s s' -> (length (st_bns s) <= length (st_bns s'))%nat;

  ek_Fr_get : forall u a s s', (length (st_bns s) <= length (st_bns s'))%nat -> scal_same s s' ->
    (forall r, r <> a -> getbn r s' = getbn r s) -> (NFIX + u <= a)%nat -> ek_Fr u [] s s';
  ek_Inv_get : forall a s s', ek_Inv s -> scal_same s s' -> (forall r, r <> a -> getbn r s' = getbn r s) ->
    (NFIX + gx_used (st_ctx s) <= a)%nat -> ek_Inv s';
  ek_rfree_pool : forall j, ek_rfree (RPool j);
  ek_wr_low : forall q, In q ek_wr -> (q < NFIX)%nat;
  ek_mulop_ok : forall u r a b F s x y,
    ek_Inv s -> (u <= gx_used (st_ctx s))%nat ->
    live r s -> live a s -> live b s -> ndiff r ROne -> ek_rfree r ->
    (length (gx_frames (st_ctx s)) + ek_D <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + ek_P <= BG_POOL)%nat ->
    ek_Rep x (getbn a s) -> ek_Rep y (getbn b s) ->
    hoare F s (ek_mulop r a b) (fun _ s' => ek_Fr u [r] s s' /\ ctx_keep s s' /\ ek_Inv s' /\ ek_Rep (x * y) (getbn r s'))
}.

Variable K : exp_kit.
Local Notation mulop := (ek_mulop K).
Local Notation Inv := (ek_Inv K).
Local Notation Rep := (ek_Rep K).
Local Notation rfree := (ek_rfree K).
Local Notation wr := (ek_wr K).
Local Notation Fr := (ek_Fr K).
Local Notation D := (ek_D K).
Local Notation P := (ek_P K).
Local Notation Fr_refl := (ek_Fr_refl K).
Local Notation Fr_trans := (ek_Fr_trans K).
Local Notation Fr_weaken := (ek_Fr_weaken K).
Local Notation Fr_slot := (ek_Fr_slot K).
Local Notation Fr_len := (ek_Fr_len K).
Local Notation Fr_get := (ek_Fr_get K).
Local Notation Inv_get := (ek_Inv_get K).
Local Notation rfree_pool := (ek_rfree_pool K).
Local Notation wr_low := (ek_wr_low K).
Local Notation mulop_ok := (ek_mulop_ok K).

Lemma exp_sqr_loop_ok : forall cnt u r F s x,
  Inv s -> (u <= gx_used (st_ctx s))%nat -> live r s -> ndiff r ROne -> rfree r ->
  (length (gx_frames (st_ctx s)) + D <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + P <= BG_POOL)%nat ->
  Rep x (getbn r s) ->
  hoare F s (exp_sqr_loop ops mulop cnt r) (fun _ s' =>
     Fr u [r] s s' /\ ctx_keep s s' /\ Inv s' /\ Rep (x ^ (2 ^ Z.of_nat cnt)) (getbn r s')).
Proof.
  induction cnt as [|c IH]; intros u r F s x HI Hu Lr Nr Rr Hd Hp HR; cbn [exp_sqr_loop].
  - apply hoare_ret. split; [apply Fr_refl|]. split; [apply ctx_keep_refl|]. split; [exact HI|].
    rewrite Z.pow_0_r, Z.pow_1_r. exact HR.
  - eapply hoare_bind; [apply (mulop_ok u r r r F s x x); assumption|].
    intros [] s1 Hs1 (F1 & C1 & I1 & R1). pose proof C1 as (L1 & U1 & Fm1).
    eapply hoare_mono.
    + apply (IH u r F s1 (x * x)); try assumption.
      * rewrite U1. exact Hu.
      * unfold live in *. rewrite U1. exact Lr.
      * rewrite Fm1. exact Hd.
      * rewrite U1. exact Hp.
    + intros [] s2 _ (F2 & C2 & I2 & R2). split; [|split; [eapply ctx_keep_trans; eassumption|split; [exact I2|]]].
      * eapply Fr_weaken; [apply Nat.le_refl| |eapply Fr_trans; [exact F1|exact F2]].
        intros q Hq _. apply in_app_or in Hq. destruct Hq as [Hq|Hq]; exact Hq.
      * rewrite pow_sqr_step in R2 by lia. rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat c)) with (Z.of_nat c + 1) by lia. exact R2.
Qed.

Definition tab (a : Z) (vals : list bnref) (s : ST) : Prop :=
  forall i, (i < length vals)%nat -> Rep (a ^ (2 * Z.of_nat i + 1)) (getbn (nth i vals 0%nat) s).

Definition tab_refs (vals : list bnref) (s : ST) : Prop :=
  forall v, In v vals -> live v s /\ ~ In v wr.

Lemma tab_frame : forall a vals u o s s',
  tab a vals s -> (forall v, In v vals -> (v < NFIX + u)%nat /\ ~ In v o /\ ~ In v wr) -> Fr u o s s' -> tab a vals s'.
Proof.
  intros a vals u o s s' HT HV HF i Hi. destruct (HV (nth i vals 0%nat) (nth_In _ _ Hi)) as (A1 & A2 & A3).
  rewrite (Fr_slot u o s s' _ HF A1 A2 A3). apply HT. exact Hi.
Qed.

Lemma last_nth : forall (l : list bnref) d, l <> [] -> last l d = nth (length l - 1) l d.
Proof.
  induction l as [|x l IH]; intros d Hne; [congruence|]. destruct l as [|y l']; [reflexivity|].
  change (last (x :: y :: l') d) with (last (y :: l') d). rewrite IH by discriminate.
  cbn [length]. destruct (length l'); reflexivity.
Qed.

Lemma exp_table_loop_ok : forall cnt vals d F s a,
  Inv s -> vals <> [] -> tab a vals s -> tab_refs vals s -> Rep (a ^ 2) (getbn d s) -> live d s -> ~ In d wr ->
  (length (gx_frames (st_ctx s)) + D <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + cnt + P <= BG_POOL)%nat -> 0 <= a ->
  hoare F s (exp_table_loop ops mulop cnt vals d) (fun vals' s' =>
     (exists new, vals' = vals ++ new /\ length new = cnt /\ forall i, (i < cnt)%nat -> nth i new 0%nat = RPool (gx_used (st_ctx s) + i)) /\
     Fr (gx_used (st_ctx s)) [] s s' /\ (length (st_bns s) <= length (st_bns s'))%nat /\
     gx_used (st_ctx s') = (gx_used (st_ctx s) + cnt)%nat /\ gx_frames (st_ctx s') = gx_frames (st_ctx s) /\
     Inv s' /\ tab a vals' s' /\ tab_refs vals' s').
Proof.
  induction cnt as [|c IH]; intros vals d F s a HI Hne HT HV HRd Ld Wd Hd Hp Ha; cbn [exp_table_loop].
  - apply hoare_ret. split; [exists []; rewrite app_nil_r; split; [reflexivity|]; split; [reflexivity|intros i Hi; lia]|].
    split; [apply Fr_refl|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [exact HI|]. split; assumption.
  - apply hoare_wf. intros Hs. set (u := gx_used (st_ctx s)) in *.
    eapply hoare_bind; [apply BN_CTX_get_spec; unfold BG_POOL in *; lia|].
    intros v s1 Hs1 (Ev & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). fold u in Ev, Eu1.
    assert (F01 : Fr u [] s s1) by (apply (Fr_get u v s s1 Len1 Sc1 Oth1); rewrite Ev; unfold RPool; lia).
    assert (I1 : Inv s1) by (apply (Inv_get v s s1 HI Sc1 Oth1); rewrite Ev; unfold RPool; fold u; lia).
    assert (Vlow : forall w, In w vals -> (w < NFIX + u)%nat /\ w <> v).
    { intros w Hw. destruct (HV w Hw) as [Lw _]. unfold live in Lw. fold u in Lw. split; [exact Lw|]. rewrite Ev. unfold RPool. lia. }
    assert (HT1 : tab a vals s1).
    { intros i Hi. rewrite Oth1 by (apply Vlow; apply nth_In; exact Hi). apply HT. exact Hi. }
    unfold live in Ld. fold u in Ld.
    eapply hoare_bind.
    { apply (mulop_ok u v (last vals 0%nat) d F s1 (a ^ (2 * Z.of_nat (length vals - 1) + 1)) (a ^ 2) I1).
      - rewrite Eu1. lia.
      - unfold live. rewrite Eu1, Ev. unfold RPool. lia.
      - unfold live. rewrite Eu1. destruct (Vlow (last vals 0%nat)) as [H _]; [|lia].
        rewrite last_nth by exact Hne. apply nth_In. destruct vals; [congruence|cbn; lia].
      - unfold live. rewrite Eu1. lia.
      - rewrite Ev. unfold ndiff, RPool, ROne, NFIX. lia.
      - rewrite Ev. apply rfree_pool.
      - rewrite Ef1. exact Hd.
      - rewrite Eu1. unfold BG_POOL in *. lia.
      - rewrite last_nth by exact Hne. apply HT1. destruct vals; [congruence|cbn; lia].
      - rewrite Oth1 by (rewrite Ev; unfold RPool; lia). exact HRd. }
    intros [] s2 Hs2 (F12 & C12 & I2 & R2). pose proof C12 as (L12 & U2 & Fm2).
    assert (HT2 : tab a (vals ++ [v]) s2).
    { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      destruct (Nat.lt_ge_cases i (length vals)) as [Hlt|Hge].
      - rewrite app_nth1 by exact Hlt. destruct (Vlow _ (nth_In vals 0%nat Hlt)) as [W1 W2].
        rewrite (Fr_slot u [v] s1 s2 _ F12 W1 ltac:(intros [E|[]]; apply W2; rewrite E; reflexivity) ltac:(apply HV; apply nth_In; exact Hlt)).
        apply HT1. exact Hlt.
      - assert (i = length vals) as -> by lia. rewrite nth_middle.
        replace (2 * Z.of_nat (length vals) + 1) with (2 * Z.of_nat (length vals - 1) + 1 + 2) by (destruct vals; [congruence|cbn [length]; lia]).
        rewrite Z.pow_add_r by lia. exact R2. }
    assert (HV2 : tab_refs (vals ++ [v]) s2).
    { intros w Hw. apply in_app_or in Hw. unfold live. rewrite U2, Eu1. destruct Hw as [Hw|[<-|[]]].
      - destruct (Vlow w Hw) as [W1 _]. destruct (HV w Hw) as [_ W3]. split; [lia|exact W3].
      - rewrite Ev. split; [unfold RPool; lia|]. intros Hin. pose proof (wr_low _ Hin). unfold RPool in *. lia. }
    eapply hoare_mono.
    { apply (IH (vals ++ [v]) d F s2 a I2); try assumption.
      - destruct vals; [congruence|discriminate].
      - rewrite (Fr_slot u [v] s1 s2 d F12 Ld ltac:(rewrite Ev; unfold RPool; intros [E|[]]; lia) Wd).
        rewrite Oth1 by (rewrite Ev; unfold RPool; lia). exact HRd.
      - unfold live. rewrite U2, Eu1. lia.
      - rewrite Fm2, Ef1. exact Hd.
      - rewrite U2, Eu1. lia. }
    intros vals' s3 _ ((new & -> & Ln & Hn) & F23 & L23 & U3 & Fm3 & I3 & HT3 & HV3). rewrite U2, Eu1 in *. rewrite Fm2, Ef1 in Fm3.
    split; [|split; [|split; [lia|split; [lia|split; [exact Fm3|split; [exact I3|split; [exact HT3|exact HV3]]]]]]].
    + exists (v :: new). rewrite <- app_assoc. cbn [app]. split; [reflexivity|]. split; [cbn [length]; lia|].
      intros i Hi. destruct i as [|i]; cbn [nth]; [rewrite Ev; f_equal; lia|]. rewrite Hn by lia. f_equal. lia.
    + assert (F2 : Fr u [] s1 s2).
      { eapply Fr_weaken; [| |exact F12]; [lia|]. intros q [<-|[]] Hq. rewrite Ev in Hq. unfold RPool in Hq. lia. }
      assert (F3 : Fr u [] s2 s3) by (eapply Fr_weaken; [| |exact F23]; [lia|intros q [] ]).
      pose proof (Fr_trans _ _ _ _ _ _ (Fr_trans _ _ _ _ _ _ F01 F2) F3) as F03. exact F03.
Qed.

Lemma exp_table_ok : forall window v0 d F s a,
  Inv s -> live v0 s -> ~ In v0 wr -> live d s -> ndiff d ROne -> rfree d -> ~ In d wr -> v0 <> d ->
  Rep a (getbn v0 s) -> 1 <= window -> 0 <= a ->
  (length (gx_frames (st_ctx s)) + D <= BG_DEPTH)%nat ->
  (Z.of_nat (gx_used (st_ctx s)) + 2 ^ (window - 1) - 1 + Z.of_nat P <= Z.of_nat BG_POOL) ->
  hoare F s (exp_table ops mulop window v0 d) (fun vals s' =>
     (exists new, vals = v0 :: new /\ forall i, (i < length new)%nat -> nth i new 0%nat = RPool (gx_used (st_ctx s) + i)) /\
     length vals = Z.to_nat (2 ^ (window - 1)) /\
     Fr (gx_used (st_ctx s)) [d] s s' /\ (length (st_bns s) <= length (st_bns s'))%nat /\
     gx_used (st_ctx s') = (gx_used (st_ctx s) + (Z.to_nat (2 ^ (window - 1)) - 1))%nat /\ gx_frames (st_ctx s') = gx_frames (st_ctx s) /\
     Inv s' /\ tab a vals s' /\ tab_refs vals s').
Proof.
  intros window v0 d F s a HI Lv Wv Ld Nd Rd Wd Hvd HR Hw Ha Hd Hp. unfold exp_table.
  set (u := gx_used (st_ctx s)) in *.
  assert (Hpw : 1 <= 2 ^ (window - 1)) by (change 1 with (2 ^ 0) at 1; apply Z.pow_le_mono_r; lia).
  assert (HT0 : tab a [v0] s).
  { intros i Hi. cbn [length] in Hi. assert (i = 0)%nat as -> by lia. cbn [nth]. rewrite Z.mul_0_r, Z.add_0_l, Z.pow_1_r. exact HR. }
  assert (HV0 : tab_refs [v0] s) by (intros w [<-|[]]; split; assumption).
  destruct (Z.ltb_spec 1 window) as [Hgt|Hle].
  - eapply hoare_bind; [apply (mulop_ok u d v0 v0 F s a a HI); try assumption; try lia; unfold BG_POOL in *; lia|].
    intros [] s1 Hs1 (F1 & C1 & I1 & R1). pose proof C1 as (L1 & U1 & Fm1).
    unfold live in Lv, Ld. fold u in Lv, Ld.
    assert (Ev0 : getbn v0 s1 = getbn v0 s) by (apply (Fr_slot u [d] s s1 v0 F1 Lv); [intros [E|[]]; apply Hvd; rewrite E; reflexivity|exact Wv]).
    eapply hoare_mono.
    { apply (exp_table_loop_ok (Z.to_nat (2 ^ (window - 1)) - 1) [v0] d F s1 a I1); try assumption.
      - discriminate.
      - intros i Hi. cbn [length] in Hi. assert (i = 0)%nat as -> by lia. cbn [nth]. rewrite Ev0. apply HT0. cbn; lia.
      - intros w [<-|[]]. split; [unfold live; rewrite U1; exact Lv|exact Wv].
      - rewrite <- Z.pow_2_r in R1. exact R1.
      - unfold live. rewrite U1. exact Ld.
      - rewrite Fm1. exact Hd.
      - rewrite U1. fold u. unfold BG_POOL in *. lia. }
    intros vals s2 _ ((new & -> & Ln & Hn) & F12 & L12 & U2 & Fm2 & I2 & HT2 & HV2). rewrite U1 in *. fold u in Hn, U2, F12.
    split; [exists new; split; [reflexivity|intros i Hi; apply Hn; lia]|].
    split; [rewrite length_app, Ln; cbn [length]; lia|].
    split; [|split; [lia|split; [exact U2|split; [rewrite Fm2; exact Fm1|split; [exact I2|split; assumption]]]]].
    replace [d] with ([d] ++ []) by reflexivity. eapply Fr_trans; [exact F1|exact F12].
  - assert (window = 1) as -> by lia. change (Z.to_nat (2 ^ (1 - 1))) with 1%nat. cbn [Nat.sub Nat.add].
    apply hoare_ret. split; [exists []; split; [reflexivity|intros i Hi; cbn in Hi; lia]|].
    split; [reflexivity|]. split; [apply Fr_refl|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [exact HI|]. split; assumption.
Qed.

Lemma nth_In_vals : forall (vals : list bnref) i, (i < length vals)%nat -> In (nth i vals 0%nat) vals.
Proof. intros. apply nth_In. assumption. Qed.

Lemma exp_window_loop_ok : forall fuel u rp r vals window wstart start F s a p,
  Inv s -> (u <= gx_used (st_ctx s))%nat ->
  live r s -> ndiff r ROne -> rfree r -> ~ In r wr ->
  (rp < NFIX + u)%nat -> ~ In rp wr -> rp <> r -> (rp < length (st_bns s))%nat ->
  (forall v, In v vals -> (v < NFIX + u)%nat /\ v <> r /\ ~ In v wr) ->
  (length (gx_frames (st_ctx s)) + D <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + P <= BG_POOL)%nat ->
  p = bn_mag (getbn rp s) -> 0 <= a -> 0 <= wstart < Z.of_nat fuel -> 1 <= window ->
  length vals = Z.to_nat (2 ^ (window - 1)) -> tab a vals s ->
  Rep (a ^ (p / 2 ^ (wstart + 1))) (getbn r s) -> (start = true -> p / 2 ^ (wstart + 1) = 0) ->
  hoare F s (exp_window_loop ops mulop fuel rp r vals window wstart start) (fun _ s' =>
     Fr u [r] s s' /\ ctx_keep s s' /\ Inv s' /\ Rep (a ^ p) (getbn r s')).
Proof.
  induction fuel as [|f IH]; intros u rp r vals window wstart start F s a p HI Hu Lr Nr Rr Wr Hrp Wrp Nrpr Vrp HV Hd Hp Ep Ha Hws Hw Lv HT HR Hst;
    [lia|]. cbn [exp_window_loop].
  apply hoare_wf. intros Hs. apply hoare_bind_get.
  pose proof (st_wf_okv rp s Hs Vrp) as OKp.
  assert (Hp0 : 0 <= p) by (rewrite Ep; apply okv_mag_nonneg; exact OKp).
  assert (Ebit : forall n, 0 <= n -> is_bit_set_pure (getbn rp s) n = Z.testbit p n) by (intros n Hn; rewrite Ep; apply is_bit_set_pure_spec; assumption).
  rewrite Ebit by lia.
  assert (Hpw : 1 <= 2 ^ (window - 1)) by (change 1 with (2 ^ 0) at 1; apply Z.pow_le_mono_r; lia).
  destruct (Z.testbit p wstart) eqn:Eb; cbn [negb].
  -
    rewrite (window_scan_ext (is_bit_set_pure (getbn rp s)) (Z.testbit p)) by exact Ebit.
    pose proof (window_scan_spec p wstart window Hp0 ltac:(lia) Hw Eb) as SC.
    destruct (window_scan (Z.testbit p) wstart (Z.to_nat (window - 1)) 1 1 0) as [wv we].
    destruct SC as (S1 & S2 & S3 & S4 & S5).
    set (e := p / 2 ^ (wstart + 1)) in *.

    eapply hoare_bind with (R := fun _ s' => Fr u [r] s s' /\ ctx_keep s s' /\ Inv s' /\ Rep ((a ^ e) ^ (2 ^ (we + 1))) (getbn r s')).
    { destruct start.
      - apply hoare_ret. split; [apply Fr_refl|]. split; [apply ctx_keep_refl|]. split; [exact HI|].
        rewrite (Hst eq_refl). rewrite Z.pow_0_r, Z.pow_1_l by (apply Z.pow_nonneg; lia). rewrite (Hst eq_refl) in HR. rewrite Z.pow_0_r in HR. exact HR.
      - eapply hoare_mono; [apply (exp_sqr_loop_ok (Z.to_nat (we + 1)) u r F s (a ^ e)); assumption|].
        intros [] s' _ (A1 & A2 & A3 & A4). rewrite Z2Nat.id in A4 by lia. auto. }
    intros [] s1 Hs1 (F1 & C1 & I1 & R1). pose proof C1 as (L1 & U1 & Fm1).

    set (i := Z.to_nat (Z.shiftr wv 1)).
    assert (Hi : (i < length vals)%nat).
    { unfold i. rewrite Lv, Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
      apply Z2Nat.inj_lt; [apply Z.div_pos; lia|lia|].
      apply Z.div_lt_upper_bound; [lia|]. replace (2 * 2 ^ (window - 1)) with (2 ^ window); [lia|].
      replace window with (window - 1 + 1) at 1 by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
    destruct (HV _ (nth_In_vals vals i Hi)) as (W1 & W2 & W3).
    assert (Hodd : 2 * Z.of_nat i + 1 = wv).
    { unfold i. rewrite Z2Nat.id by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite (Z.div_mod wv 2) at 2 by lia.
      rewrite Zmod_odd, S4. lia. }
    eapply hoare_bind.
    { apply (mulop_ok u r r (@nth bnref i vals 0%nat) F s1 ((a ^ e) ^ (2 ^ (we + 1))) (a ^ (2 * Z.of_nat i + 1)) I1).
      - rewrite U1. exact Hu.
      - unfold live in *. rewrite U1. exact Lr.
      - unfold live in *. rewrite U1. exact Lr.
      - unfold live. rewrite U1. apply (Nat.lt_le_trans _ _ _ W1). apply Nat.add_le_mono_l. exact Hu.
      - exact Nr.
      - exact Rr.
      - rewrite Fm1. exact Hd.
      - rewrite U1. exact Hp.
      - exact R1.
      - rewrite (Fr_slot u [r] s s1 _ F1 W1 ltac:(intros [E|[]]; apply W2; rewrite E; reflexivity) W3). apply HT. exact Hi. }
    intros [] s2 Hs2 (F2 & C2 & I2 & R2). pose proof C2 as (L2 & U2 & Fm2).

    rewrite Hodd, S3 in R2. rewrite pow_window_step in R2 by (try (unfold e; apply Z.div_pos); try apply Z.mod_pos_bound; try apply Z.pow_pos_nonneg; unfold bits_val; try lia;
      try (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia)).
    unfold e in R2. rewrite <- (exp_window_step p wstart we Hp0 ltac:(lia)) in R2.
    assert (F02 : Fr u [r] s s2).
    { eapply Fr_weaken; [apply Nat.le_refl| |eapply Fr_trans; [exact F1|exact F2]].
      intros q Hq _. apply in_app_or in Hq. destruct Hq as [Hq|Hq]; exact Hq. }
    pose proof (ctx_keep_trans _ _ _ C1 C2) as C02.
    destruct (Z.ltb_spec (wstart - (we + 1)) 0) as [Hend|Hmore].
    +
      apply hoare_ret. split; [exact F02|]. split; [exact C02|]. split; [exact I2|].
      assert (we = wstart) as -> by lia. rewrite Z.sub_diag, Z.pow_0_r, Z.div_1_r in R2. exact R2.
    + eapply hoare_mono.
      { apply (IH u rp r vals window (wstart - (we + 1)) false F s2 a p I2); try assumption; try lia.
        - unfold live in *. rewrite U2, U1. exact Lr.
        - rewrite Fm2, Fm1. exact Hd.
        - rewrite (Fr_slot u [r] s s2 rp F02 Hrp ltac:(intros [E|[]]; apply Nrpr; rewrite E; reflexivity) Wrp). exact Ep.
        - eapply tab_frame; [exact HT| |exact F02]. intros v Hv. destruct (HV v Hv) as (A1 & A2 & A3).
          split; [exact A1|]. split; [intros [E|[]]; apply A2; rewrite E; reflexivity|exact A3].
        - replace (wstart - (we + 1) + 1) with (wstart - we) by lia. exact R2. }
      intros [] s3 _ (F3 & C3 & I3 & R3). split; [|split; [eapply ctx_keep_trans; eassumption|split; [exact I3|exact R3]]].
      eapply Fr_weaken; [apply Nat.le_refl| |eapply Fr_trans; [exact F02|exact F3]].
      intros q Hq _. apply in_app_or in Hq. destruct Hq as [Hq|Hq]; exact Hq.
  -
    set (e := p / 2 ^ (wstart + 1)) in *.
    eapply hoare_bind with (R := fun _ s' => Fr u [r] s s' /\ ctx_keep s s' /\ Inv s' /\ Rep (a ^ (p / 2 ^ wstart)) (getbn r s') /\
                                         (start = true -> p / 2 ^ wstart = 0)).
    { pose proof (exp_zero_bit p wstart Hp0 ltac:(lia) Eb) as Ez. fold e in Ez.
      destruct start.
      - apply hoare_ret. split; [apply Fr_refl|]. split; [apply ctx_keep_refl|]. split; [exact HI|].
        rewrite Ez, (Hst eq_refl). rewrite (Hst eq_refl) in HR. split; [exact HR|reflexivity].
      - eapply hoare_mono; [apply (mulop_ok u r r r F s (a ^ e) (a ^ e) HI); assumption|].
        intros [] s' _ (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
        split; [|intros E; discriminate E]. rewrite Ez. rewrite <- Z.pow_2_r, <- Z.pow_mul_r, (Z.mul_comm e 2) in A4 by (try unfold e; try apply Z.div_pos; lia). exact A4. }
    intros [] s1 Hs1 (F1 & C1 & I1 & R1 & Hst1). pose proof C1 as (L1 & U1 & Fm1).
    destruct (Z.eqb_spec wstart 0) as [->|Hne].
    + apply hoare_ret. split; [exact F1|]. split; [exact C1|]. split; [exact I1|].
      rewrite Z.pow_0_r, Z.div_1_r in R1. exact R1.
    + eapply hoare_mono.
      { apply (IH u rp r vals window (wstart - 1) start F s1 a p I1); try assumption; try lia.
        - unfold live in *. rewrite U1. exact Lr.
        - rewrite Fm1. exact Hd.
        - rewrite (Fr_slot u [r] s s1 rp F1 Hrp ltac:(intros [E|[]]; apply Nrpr; rewrite E; reflexivity) Wrp). exact Ep.
        - eapply tab_frame; [exact HT| |exact F1]. intros v Hv. destruct (HV v Hv) as (A1 & A2 & A3).
          split; [exact A1|]. split; [intros [E|[]]; apply A2; rewrite E; reflexivity|exact A3].
        - replace (wstart - 1 + 1) with wstart by lia. exact R1.
        - replace (wstart - 1 + 1) with wstart by lia. exact Hst1. }
      intros [] s3 _ (F3 & C3 & I3 & R3). split; [|split; [eapply ctx_keep_trans; eassumption|split; [exact I3|exact R3]]].
      eapply Fr_weaken; [apply Nat.le_refl| |eapply Fr_trans; [exact F1|exact F3]].
      intros q Hq _. apply in_app_or in Hq. destruct Hq as [Hq|Hq]; exact Hq.
Qed.

End ExpLoops.
