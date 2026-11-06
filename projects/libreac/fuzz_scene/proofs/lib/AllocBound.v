From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO03 YO0j YO0m YO0o YO0u YO0x YO10.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import AllocSI AllocGS AllocCount.
Import ListNotations.
Local Open Scope Z_scope.

Definition zsum {A} (f : A -> Z) (l : list A) : Z := fold_right (fun x acc => f x + acc) 0 l.

Lemma zsum_nil {A} (f : A -> Z) : zsum f [] = 0.
Proof. reflexivity. Qed.

Lemma zsum_cons {A} (f : A -> Z) x l : zsum f (x :: l) = f x + zsum f l.
Proof. reflexivity. Qed.

Lemma zsum_app {A} (f : A -> Z) l1 l2 : zsum f (l1 ++ l2) = zsum f l1 + zsum f l2.
Proof. induction l1 as [|x l1 IH]; cbn [app]; [rewrite zsum_nil; lia|]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_map {A B} (f : B -> Z) (g : A -> B) l : zsum f (map g l) = zsum (fun x => f (g x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons, IH. reflexivity. Qed.

Lemma zsum_nonneg {A} (f : A -> Z) l : (forall x, In x l -> 0 <= f x) -> 0 <= zsum f l.
Proof.
  induction l as [|x l IH]; intros H; [rewrite zsum_nil; lia|]. rewrite zsum_cons.
  pose proof (H x (or_introl eq_refl)). assert (0 <= zsum f l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsum_remove {B} (dec : forall x y : B, {x = y} + {x <> y}) (w : B -> Z) b :
  forall m, In b m -> (forall x, In x m -> 0 <= w x) -> w b + zsum w (remove dec b m) <= zsum w m.
Proof.
  induction m as [|x m IH]; intros Hin Hw; [destruct Hin|].
  cbn [remove]. rewrite zsum_cons. pose proof (Hw x (or_introl eq_refl)) as Hx.
  assert (Hw' : forall y, In y m -> 0 <= w y) by (intros y Hy; apply Hw; right; exact Hy).
  destruct (dec b x) as [<-|N].
  - destruct (in_dec dec b m) as [Hm|Hm].
    + pose proof (IH Hm Hw'). lia.
    + rewrite (@notin_remove _ dec m b Hm). lia.
  - rewrite zsum_cons. destruct Hin as [E|Hin]; [congruence|]. pose proof (IH Hin Hw'). lia.
Qed.

Lemma ac_wsum {A B} (dec : forall x y : B, {x = y} + {x <> y}) (R : A -> B -> Prop) (c : A -> Z) (w : B -> Z) :
  forall l m, NoDup l -> (forall x, In x m -> 0 <= w x) ->
  (forall a, In a l -> c a <= 0 \/ exists b, In b m /\ R a b /\ c a <= w b) ->
  (forall a a' b, In a l -> In a' l -> R a b -> R a' b -> a = a') ->
  zsum c l <= zsum w m.
Proof.
  induction l as [|a l IH]; intros m Hnd Hw Hex Hinj.
  - rewrite zsum_nil. apply zsum_nonneg. exact Hw.
  - apply NoDup_cons_iff in Hnd as [Hna Hnd]. rewrite zsum_cons.
    assert (Hinj' : forall x y z, In x l -> In y l -> R x z -> R y z -> x = y)
      by (intros x y z Hx Hy; apply Hinj; right; assumption).
    destruct (Hex a (or_introl eq_refl)) as [Hc | (b & Hb & Rb & Hcb)].
    + assert (zsum c l <= zsum w m); [|lia].
      apply IH; [exact Hnd | exact Hw | intros a' Ha'; apply Hex; right; exact Ha' | exact Hinj'].
    + pose proof (zsum_remove dec w b m Hb Hw) as Hr.
      assert (zsum c l <= zsum w (remove dec b m)); [|lia].
      apply IH; [exact Hnd | | | exact Hinj'].
      * intros x Hx. apply (@in_remove _ dec) in Hx as [Hx _]. apply Hw. exact Hx.
      * intros a' Ha'. destruct (Hex a' (or_intror Ha')) as [Hc | (b' & Hb' & Rb' & Hc)]; [left; exact Hc|right].
        exists b'. split; [|split; [exact Rb'|exact Hc]]. apply (@in_in_remove _ dec); [|exact Hb'].
        intros E. subst b'. apply Hna.
        rewrite <- (Hinj a' a b (or_intror Ha') (or_introl eq_refl) Rb' Rb). exact Ha'.
Qed.

Lemma rsum_idx (f : region -> Z) l :
  rsum f l = zsum (fun k => match nth_error l k with Some rg => f rg | None => 0 end) (seq 0 (length l)).
Proof.
  induction l as [|r l IH]; [reflexivity|].
  rewrite rsum_cons, IH. cbn [length seq]. rewrite zsum_cons, <- seq_shift, zsum_map. reflexivity.
Qed.

Lemma rsum_ge (f : region -> Z) l : forall k rg, (forall r, In r l -> 0 <= f r) -> nth_error l k = Some rg -> f rg <= rsum f l.
Proof.
  induction l as [|x l IH]; intros k rg Hn Hk; [destruct k; cbn in Hk; discriminate|].
  rewrite rsum_cons. assert (Hn' : forall r, In r l -> 0 <= f r) by (intros; apply Hn; right; assumption).
  destruct k as [|k]; cbn in Hk.
  - injection Hk as ->. pose proof (rsum_nonneg f l Hn'). lia.
  - pose proof (IH k rg Hn' Hk). pose proof (Hn x (or_introl eq_refl)). lia.
Qed.

Definition bdec (x y : Z * option (sptr * Z)) : {x = y} + {x <> y}.
Proof.
  destruct x as [a o], y as [c o'].
  destruct (Z.eq_dec a c) as [<-|N]; [|right; congruence].
  destruct o as [[p n]|], o' as [[q m]|].
  - destruct (ac_sdec p q) as [<-|N]; [|right; congruence].
    destruct (Z.eq_dec n m) as [<-|N]; [left; reflexivity|right; congruence].
  - right; congruence.
  - right; congruence.
  - left; reflexivity.
Defined.

Definition mB (bl : list (sptr * Z)) : list (Z * option (sptr * Z)) :=
  map (fun c => (c, None)) (zseq 0 48) ++ map (fun b => (0, Some b)) bl.

Definition wB (x : Z * option (sptr * Z)) : Z :=
  match snd x with None => MMAX | Some b => MMAX + snd b end.

Definition RB (s : astate) (k : nat) (x : Z * option (sptr * Z)) : Prop :=
  exists g ag, usedX [] s g ag /\ prid (am_mem ag) = k /\
  match snd x with None => frameless ag /\ am_sc ag = fst x | Some b => exists n, witn s (fst b) n g end.

Lemma MM : MMAX = 8388608.
Proof. reflexivity. Qed.

Lemma zsum_mB bl : zsum wB (mB bl) = MMAX * 48 + MMAX * Z.of_nat (length bl) + zsum snd bl.
Proof.
  unfold mB. rewrite zsum_app.
  assert (A1 : forall l : list Z, zsum wB (map (fun c => (c, None)) l) = MMAX * Z.of_nat (length l)).
  { induction l as [|c l IH]; cbn [map length]; [rewrite zsum_nil; lia|]. rewrite zsum_cons, IH. unfold wB at 1. cbn [snd]. lia. }
  assert (A2 : forall l : list (sptr * Z), zsum wB (map (fun b => (0, Some b)) l) = MMAX * Z.of_nat (length l) + zsum snd l).
  { induction l as [|b l IH]; cbn [map length]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons, IH. unfold wB at 1. cbn [snd]. lia. }
  rewrite A1, A2, zseq48. lia.
Qed.

Lemma ub_pair s (HW : WF s) g am i fr :
  usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser ->
  In (frame_ptr am i fr, fr_n fr) (user_blocks s).
Proof.
  intros U Hi F K. unfold user_blocks. apply in_flat_map. exists (g, am).
  split; [apply (used_metas_usedX s g am HW); exact U|].
  cbn [snd]. apply in_flat_map. exists i. split; [apply In_zseq; lia|].
  cbv beta. rewrite F. cbv beta iota. rewrite K. cbv beta iota. left. reflexivity.
Qed.

Lemma ub_nonneg s (HW : WF s) b : In b (user_blocks s) -> 0 <= snd b.
Proof.
  destruct b as [p n]. intros Hin.
  destruct (user_blocks_frame s p n HW Hin) as (g & am & i & fr & U & Hi & F & _ & En & _).
  cbn [snd]. rewrite <- En.
  pose proof (inv_groups HW g am U) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & T). rewrite F in T.
  destruct T as (_ & _ & (N & _) & _). exact N.
Qed.

Theorem map_bytes_bound : forall s, WF s -> SI s -> GS s -> map_bytes s <= MMAX * (nblocks s + 48) + ubytes s.
Proof.
  intros s HW HS HG. unfold map_bytes. rewrite rsum_idx.
  assert (L : zsum (fun k => match nth_error (st_regions s) k with Some rg => f_mapb rg | None => 0 end)
    (seq 0 (length (st_regions s))) <= zsum wB (mB (user_blocks s))).
  { apply (ac_wsum bdec (RB s)).
    - apply seq_NoDup.
    - intros x Hx. unfold mB in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_map_iff in Hx as (y & <- & Hy);
        unfold wB; cbn [snd]; rewrite MM; [lia|]. pose proof (ub_nonneg s HW y Hy). lia.
    - intros k _. cbv beta.
      destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; cbv beta iota; [|left; lia].
      unfold f_mapb. destruct (rg_live rg && is_map rg) eqn:E; cbv beta iota; [right|left; lia].
      apply andb_true_iff in E as [Lv Mp].
      assert (Kd : rg_kind rg = RkMap) by (unfold is_map in Mp; destruct (rg_kind rg); try discriminate; reflexivity).
      pose proof HS as (OM & EO & _).
      destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mpos & Pk).
      pose proof (inv_groups HW g ag U) as (_ & _ & _ & Gc & Gmp & _).
      destruct (Gmp Mpos) as (r & rg' & Em & Hr' & _ & _ & Len & _).
      rewrite Em in Pk. cbn in Pk. subst r. unfold region_of in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
      rewrite Len.
      destruct (HG g ag U Mpos) as [G48 G63].
      destruct (frameless_dec ag) as [FL | Hx].
      + destruct (EO g ag U FL (ac_unres g)) as [_ C].
        exists (am_sc ag, None). split.
        * unfold mB. apply in_app_iff. left. apply in_map_iff. exists (am_sc ag). split; [reflexivity | apply In_zseq; lia].
        * split.
          -- exists g, ag. split; [exact U|]. split; [rewrite Em; reflexivity|]. split; [exact FL|reflexivity].
          -- unfold wB. cbn [snd]. apply G48. lia.
      + destruct (sc_range s HW g ag U) as [E63 | E48].
        * destruct Gc as [(_ & L0 & _ & _ & _ & [E0 | (fr & F & K & _)]) | (C & _)]; [discriminate | | lia].
          exists (0, Some (frame_ptr ag 0 fr, fr_n fr)). split.
          -- unfold mB. apply in_app_iff. right. apply in_map_iff. exists (frame_ptr ag 0 fr, fr_n fr).
             split; [reflexivity | exact (ub_pair s HW g ag 0 fr U ltac:(lia) F K)].
          -- split.
             ++ exists g, ag. split; [exact U|]. split; [rewrite Em; reflexivity|]. exists O. exists 0.
                exact (find_frame_in_spec [] None U0 s HW g ag 0 fr U ltac:(lia) F).
             ++ unfold wB. cbn [snd]. pose proof (G63 E63 fr F). rewrite MM. unfold PGSZ in *. lia.
        * destruct (wit_ex s HW HS g ag U Hx) as (bp & n & Hb & W).
          apply in_map_iff in Hb as (b & Eb & Hb).
          exists (0, Some b). split.
          -- unfold mB. apply in_app_iff. right. apply in_map_iff. exists b. split; [reflexivity|exact Hb].
          -- split.
             ++ exists g, ag. split; [exact U|]. split; [rewrite Em; reflexivity|]. exists n. rewrite Eb. exact W.
             ++ unfold wB. cbn [snd]. pose proof (ub_nonneg s HW b Hb). pose proof (G48 ltac:(lia)). lia.
    - intros k k' [c o] _ _ (g & a & U & Pk & H) (g' & a' & U' & Pk' & H'). subst k k'.
      destruct o as [b|]; cbn [fst snd] in H, H'.
      + destruct H as (n & W), H' as (n' & W').
        rewrite (witn_prid s HW (fst b) n g a W U), (witn_prid s HW (fst b) n' g' a' W' U'). reflexivity.
      + destruct H as (FL & E), H' as (FL' & E'). pose proof HS as (_ & _ & EU & _).
        rewrite (EU g a g' a' U U' FL FL' (ac_unres g) (ac_unres g') ltac:(lia)) in U.
        rewrite (usedX_fun _ _ _ _ _ U U'). reflexivity. }
  rewrite zsum_mB in L. unfold nblocks.
  assert (Eu : ubytes s = zsum snd (user_blocks s)) by reflexivity.
  rewrite Eu. rewrite MM in L |- *. lia.
Qed.

Lemma resv_ge s r rg : regs_nn s -> region_of s r = Some rg -> rg_kind rg = RkMetaRes -> rg_len rg <= resv_total s.
Proof.
  intros NN Hr Kd. rewrite resv_total_rsum. unfold region_of in Hr.
  assert (Hf : rg_len rg = f_resvb rg) by (unfold f_resvb, is_resv; rewrite Kd; reflexivity).
  rewrite Hf. apply (rsum_ge f_resvb (st_regions s) r rg); [|exact Hr].
  intros x Hx. unfold f_resvb. destruct (is_resv x); [exact (NN x Hx)|lia].
Qed.

Lemma acnt_bound s : WF s -> II s -> acnt s <= 2 * 2 ^ shift s.
Proof.
  intros HW HII. pose proof HII as (NN & Hsh & Hac & _ & Hrt & _).
  pose proof (Z.pow_pos_nonneg 2 (shift s) ltac:(lia) Hsh) as P.
  destruct (Z_le_gt_dec (acnt s) 0) as [Z0|Pos]; [lia|].
  assert (Pos' : 0 < st_avail_meta_area_count s) by (unfold acnt in Pos; lia).
  destruct (inv_areas HW) as (_ & _ & _ & _ & _ & _ & _ & AV & _).
  destruct (AV Pos') as (r & o & rg & _ & Hr & Kd & _ & _ & Ho & Olen & _).
  pose proof (resv_ge s r rg NN Hr Kd) as Hle. rewrite Hrt in Hle.
  unfold acnt, PGSZ in *. lia.
Qed.

Theorem meta_bounds : forall s, WF s -> II s ->
  brk_bytes s <= 2 * PGSZ * (hand s / METAS_PER_AREA + 1 + 2 * shcap (hand s)) /\
  resv_count s <= shcap (hand s) /\
  resv_total s <= 2 * PGSZ * shcap (hand s) /\
  area s <= 2 * PGSZ * shcap (hand s).
Proof.
  intros s HW HII. pose proof (shcap_ok s HII) as SC. pose proof (acnt_bound s HW HII) as AC.
  pose proof HII as (_ & Hsh & Hac & Hamc & Hrt & Hrc & _ & Hbrk & _).
  assert (NA : nareas s - 1 <= hand s / METAS_PER_AREA).
  { apply Z.div_le_lower_bound; [unfold METAS_PER_AREA; lia|]. unfold hand, METAS_PER_AREA in *. lia. }
  unfold area. unfold PGSZ in *. repeat split; lia.
Qed.

Lemma shcap_cap h c : 0 <= h <= 49 * c + 48 -> shcap h <= shcap (49 * c + 48).
Proof. intros H. apply shcap_mono. lia. Qed.
