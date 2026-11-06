From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0j YO0m YO0u YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import AllocSI.
Import ListNotations.
Local Open Scope Z_scope.

Definition ac_sdec (p q : sptr) : {p = q} + {p <> q}.
Proof.
  destruct p as [r o], q as [r' o'].
  destruct (Nat.eq_dec r r') as [<-|N]; [|right; congruence].
  destruct (Z.eq_dec o o') as [<-|N]; [left; reflexivity|right; congruence].
Defined.

Definition ac_kdec (x y : Z * option sptr) : {x = y} + {x <> y}.
Proof.
  destruct x as [a o], y as [b o'].
  destruct (Z.eq_dec a b) as [<-|N]; [|right; congruence].
  destruct o as [p|], o' as [q|].
  - destruct (ac_sdec p q) as [<-|N]; [left; reflexivity|right; congruence].
  - right; congruence.
  - right; congruence.
  - left; reflexivity.
Defined.

Lemma ac_count {A B} (dec : forall x y : B, {x = y} + {x <> y}) (R : A -> B -> Prop) :
  forall (l : list A) (m : list B), NoDup l ->
  (forall a, In a l -> exists b, In b m /\ R a b) ->
  (forall a a' b, In a l -> In a' l -> R a b -> R a' b -> a = a') ->
  (length l <= length m)%nat.
Proof.
  induction l as [|a l IH]; intros m Hnd Hex Hinj; cbn [length]; [lia|].
  apply NoDup_cons_iff in Hnd as [Hna Hnd].
  destruct (Hex a (or_introl eq_refl)) as (b & Hb & Rb).
  pose proof (@remove_length_lt _ dec m b Hb) as Hlt.
  enough (length l <= length (remove dec b m))%nat by lia.
  apply IH; [exact Hnd| |].
  - intros a' Ha'. destruct (Hex a' (or_intror Ha')) as (b' & Hb' & Rb').
    exists b'. split; [|exact Rb']. apply (@in_in_remove _ dec); [|exact Hb'].
    intros E. subst b'. apply Hna.
    rewrite <- (Hinj a' a b (or_intror Ha') (or_introl eq_refl) Rb' Rb). exact Ha'.
  - intros x y z Hx Hy. apply Hinj; right; assumption.
Qed.

Lemma frameless_dec am :
  frameless am \/ exists i fr, 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr.
Proof.
  destruct (existsb (fun i => match ss_fr (nth_slot am i) with Some _ => true | None => false end)
    (zseq 0 (am_last am + 1))) eqn:E.
  - right. apply existsb_exists in E as (i & Hi & Hf). apply In_zseq in Hi.
    destruct (ss_fr (nth_slot am i)) as [fr|] eqn:F; [|discriminate].
    exists i, fr. split; [lia|exact F].
  - left. intros i Hi. destruct (ss_fr (nth_slot am i)) as [fr|] eqn:F; [|reflexivity]. exfalso.
    assert (Hin : In i (zseq 0 (am_last am + 1))) by (apply In_zseq; lia).
    rewrite <- Bool.not_true_iff_false in E. apply E. apply existsb_exists.
    exists i. split; [exact Hin|]. rewrite F. reflexivity.
Qed.

Lemma ac_unres g : unreserved None g.
Proof. intros i E. discriminate. Qed.

Lemma ac_padd0 p : padd p 0 = p.
Proof. destruct p; cbn; f_equal; lia. Qed.

Lemma ffi_in l p g i :
  find_frame_in l p = Some (g, i) -> exists am, In (g, MUsed am) l /\ prid p = prid (am_mem am).
Proof.
  induction l as [|[m x] t IH]; intros H; [cbn in H; discriminate|].
  destruct x as [pr nx| |am]; cbn [find_frame_in] in H.
  - destruct (IH H) as (am & Hin & Hp). exists am. split; [right; exact Hin | exact Hp].
  - destruct (IH H) as (am & Hin & Hp). exists am. split; [right; exact Hin | exact Hp].
  - destruct (find_in_slots (am_slots am) (padd (am_mem am) UNIT) (stride_of am) 0 p) as [k|] eqn:E.
    + injection H as <- <-. destruct (find_in_slots_sound _ _ _ _ _ _ E) as (x & fr & _ & _ & _ & Hp).
      exists am. split; [left; reflexivity|]. rewrite <- Hp, !prid_padd. reflexivity.
    + destruct (IH H) as (am' & Hin & Hp). exists am'. split; [right; exact Hin | exact Hp].
Qed.

Lemma ffi_used s (HW : WF s) p g i :
  find_frame_in (st_metas s) p = Some (g, i) -> exists am, usedX [] s g am /\ prid (am_mem am) = prid p.
Proof.
  intros H. destruct (ffi_in _ _ _ _ H) as (am & Hin & Hp). exists am. split; [|symmetry; exact Hp].
  apply usedX_intro; [reflexivity|]. unfold MT. apply mlookup_of_In; [exact (proj1 (inv_keys HW)) | exact Hin].
Qed.

Lemma sc_range s (HW : WF s) g am : usedX [] s g am -> am_sc am = 63 \/ 0 <= am_sc am < 48.
Proof.
  intros U. pose proof (inv_groups HW g am U) as (_ & _ & _ & Gc & _).
  destruct Gc as [(C & _) | (C & _)]; [left|right]; exact C.
Qed.

Definition wbase (s : astate) (b g : sptr) : Prop :=
  exists i, find_frame_in (st_metas s) b = Some (g, i).

Definition wpar (s : astate) (c g : sptr) : Prop :=
  exists ac i, usedX [] s c ac /\ am_maplen ac = 0 /\ find_frame_in (st_metas s) (am_mem ac) = Some (g, i).

Fixpoint witn (s : astate) (b : sptr) (n : nat) (g : sptr) : Prop :=
  match n with
  | O => wbase s b g
  | S n' => exists c, witn s b n' c /\ wpar s c g
  end.

Lemma wbase_fun s b g1 g2 : wbase s b g1 -> wbase s b g2 -> g1 = g2.
Proof. intros [i1 H1] [i2 H2]. rewrite H1 in H2. congruence. Qed.

Lemma wpar_fun s c g1 g2 : wpar s c g1 -> wpar s c g2 -> g1 = g2.
Proof.
  intros (a1 & i1 & U1 & _ & H1) (a2 & i2 & U2 & _ & H2).
  rewrite (usedX_fun _ _ _ _ _ U1 U2) in H1. rewrite H1 in H2. congruence.
Qed.

Lemma witn_fun s b n : forall g1 g2, witn s b n g1 -> witn s b n g2 -> g1 = g2.
Proof.
  induction n as [|n IH]; cbn [witn]; intros g1 g2 H1 H2.
  - exact (wbase_fun s b g1 g2 H1 H2).
  - destruct H1 as (c1 & W1 & P1), H2 as (c2 & W2 & P2).
    rewrite (IH c1 c2 W1 W2) in P1. exact (wpar_fun s c2 g1 g2 P1 P2).
Qed.

Lemma witn_used s (HW : WF s) b n g : witn s b n g -> exists ag, usedX [] s g ag.
Proof.
  destruct n as [|n]; cbn [witn].
  - intros [i H]. destruct (ffi_used s HW _ _ _ H) as (ag & U & _). exists ag. exact U.
  - intros (c & _ & ac & i & _ & _ & H). destruct (ffi_used s HW _ _ _ H) as (ag & U & _). exists ag. exact U.
Qed.

Lemma witn_prid s (HW : WF s) b n : forall g ag, witn s b n g -> usedX [] s g ag -> prid (am_mem ag) = prid b.
Proof.
  induction n as [|n IH]; cbn [witn]; intros g ag H Hu.
  - destruct H as [i H]. destruct (ffi_used s HW _ _ _ H) as (ag' & U' & E).
    rewrite (usedX_fun _ _ _ _ _ Hu U'). exact E.
  - destruct H as (c & W & ac & i & Uc & _ & H). destruct (ffi_used s HW _ _ _ H) as (ag' & U' & E).
    rewrite (usedX_fun _ _ _ _ _ Hu U'), E. exact (IH c ac W Uc).
Qed.

Lemma wpar_sc s (HW : WF s) c ac g ag :
  wpar s c g -> usedX [] s c ac -> usedX [] s g ag -> am_sc ac < am_sc ag.
Proof.
  intros (ac' & i & Uc & M0 & H) Hc Hg. rewrite (usedX_fun _ _ _ _ _ Uc Hc) in M0, H.
  pose proof (inv_groups HW c ac Hc) as (_ & _ & _ & _ & _ & Gn).
  destruct (Gn M0) as (_ & g' & am' & i' & fr' & U' & Hi' & F' & K' & Mem & Sc & _).
  destruct (fgroup_frame [] None U0 s HW g' am' i' fr' U' Hi' F' K') as [_ Off].
  pose proof (find_frame_in_spec [] None U0 s HW g' am' i' fr' U' Hi' F') as Hf.
  unfold frame_ptr in Hf. rewrite Off, Z.mul_0_r, ac_padd0, <- Mem, H in Hf.
  injection Hf as Eg _. subst g. rewrite (usedX_fun _ _ _ _ _ Hg U'). exact Sc.
Qed.

Lemma witn_sc s (HW : WF s) b n : forall k c g ac ag,
  witn s b n c -> witn s b (n + S k) g -> usedX [] s c ac -> usedX [] s g ag -> am_sc ac < am_sc ag.
Proof.
  intros k. induction k as [|k IH]; intros c g ac ag Wc Wg Uc Ug.
  - rewrite Nat.add_1_r in Wg. cbn [witn] in Wg. destruct Wg as (c' & W' & P).
    rewrite (witn_fun s b n c' c W' Wc) in P. exact (wpar_sc s HW c ac g ag P Uc Ug).
  - rewrite Nat.add_succ_r in Wg. cbn [witn] in Wg. destruct Wg as (c' & W' & P).
    destruct (witn_used s HW b _ c' W') as (ac' & U').
    pose proof (IH c c' ac ac' Wc W' Uc U'). pose proof (wpar_sc s HW c' ac' g ag P U' Ug). lia.
Qed.

Lemma wit_inj s (HW : WF s) b n1 n2 g1 a1 g2 a2 :
  witn s b n1 g1 -> witn s b n2 g2 -> usedX [] s g1 a1 -> usedX [] s g2 a2 -> am_sc a1 = am_sc a2 -> g1 = g2.
Proof.
  intros W1 W2 U1 U2 E.
  destruct (lt_eq_lt_dec n1 n2) as [[L|<-]|L].
  - exfalso. replace n2 with (n1 + S (n2 - n1 - 1))%nat in W2 by lia.
    pose proof (witn_sc s HW b n1 _ g1 g2 a1 a2 W1 W2 U1 U2). lia.
  - exact (witn_fun s b n1 g1 g2 W1 W2).
  - exfalso. replace n1 with (n2 + S (n1 - n2 - 1))%nat in W1 by lia.
    pose proof (witn_sc s HW b n2 _ g2 g1 a2 a1 W2 W1 U2 U1). lia.
Qed.

Lemma ub_in s (HW : WF s) g am i fr :
  usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser ->
  In (frame_ptr am i fr) (map fst (user_blocks s)).
Proof.
  intros U Hi F K. apply in_map_iff. exists (frame_ptr am i fr, fr_n fr). split; [reflexivity|].
  unfold user_blocks. apply in_flat_map. exists (g, am).
  split; [apply (used_metas_usedX s g am HW); exact U|].
  cbn [snd]. apply in_flat_map. exists i. split; [apply In_zseq; lia|].
  cbv beta. rewrite F. cbv beta iota. rewrite K. cbv beta iota. left. reflexivity.
Qed.

Lemma wit_exists s (HW : WF s) (HS : SI s) k : forall g am, usedX [] s g am -> (Z.to_nat (am_sc am) < k)%nat ->
  (exists i fr, 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr) ->
  exists b n, In b (map fst (user_blocks s)) /\ witn s b n g.
Proof.
  induction k as [|k IH]; intros g am U Hk (i & fr & Hi & F); [lia|].
  destruct (fr_kind fr) eqn:K.
  - exists (frame_ptr am i fr), O. split; [exact (ub_in s HW g am i fr U Hi F K)|].
    exists i. exact (find_frame_in_spec [] None U0 s HW g am i fr U Hi F).
  - pose proof HS as (_ & EO & _ & CO & _).
    destruct (CO g am i fr U Hi F K) as (c & ac & Uc & M0 & Mem & Sc).
    assert (Hc : exists j fj, 0 <= j <= am_last ac /\ ss_fr (nth_slot ac j) = Some fj).
    { destruct (frameless_dec ac) as [FL|Hx]; [|exact Hx].
      destruct (EO c ac Uc FL (ac_unres c)) as [Hp _]. lia. }
    assert (Hk' : (Z.to_nat (am_sc ac) < k)%nat) by (destruct (sc_range s HW c ac Uc); lia).
    destruct (IH c ac Uc Hk' Hc) as (b & n & Hb & W).
    exists b, (S n). split; [exact Hb|]. exists c. split; [exact W|].
    exists ac, i. split; [exact Uc|]. split; [exact M0|].
    destruct (fgroup_frame [] None U0 s HW g am i fr U Hi F K) as [_ Off].
    pose proof (find_frame_in_spec [] None U0 s HW g am i fr U Hi F) as Hf.
    unfold frame_ptr in Hf. rewrite Off, Z.mul_0_r, ac_padd0, <- Mem in Hf. exact Hf.
Qed.

Lemma wit_ex s (HW : WF s) (HS : SI s) g am : usedX [] s g am ->
  (exists i fr, 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr) ->
  exists b n, In b (map fst (user_blocks s)) /\ witn s b n g.
Proof. intros U Hx. apply (wit_exists s HW HS (S (Z.to_nat (am_sc am))) g am U); [lia|exact Hx]. Qed.

Lemma zseq48 : length (zseq 0 48) = 48%nat.
Proof. reflexivity. Qed.

Lemma flat_len (cs : list Z) (bl : list sptr) :
  length (flat_map (fun c => map (fun b => (c, Some b)) bl) cs) = (length cs * length bl)%nat.
Proof. induction cs as [|c cs IH]; cbn [flat_map length]; [reflexivity|]. rewrite length_app, length_map, IH. reflexivity. Qed.

Lemma len_filter_map {A B} (f : B -> bool) (g : A -> B) (l : list A) :
  length (filter f (map g l)) = length (filter (fun x => f (g x)) l).
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (f (g x)); cbn; rewrite IH; reflexivity. Qed.

Lemma mapc_count l : rsum f_mapc l = Z.of_nat (length (filter (fun k =>
  match nth_error l k with Some rg => rg_live rg && is_map rg | None => false end) (seq 0 (length l)))).
Proof.
  induction l as [|r l IH]; [reflexivity|].
  rewrite rsum_cons, IH. cbn [length seq]. rewrite <- seq_shift. cbn [filter nth_error].
  unfold f_mapc. destruct (rg_live r && is_map r); cbn [length]; rewrite len_filter_map; cbn [nth_error]; lia.
Qed.

Definition mT4 (bl : list sptr) : list (Z * option sptr) :=
  map (fun c => (c, None)) (zseq 0 48) ++ map (fun b => (0, Some b)) bl.

Definition mT5 (bl : list sptr) : list (Z * option sptr) :=
  map (fun c => (c, None)) (zseq 0 48) ++ flat_map (fun c => map (fun b => (c, Some b)) bl) (zseq 0 48 ++ [63]).

Definition R4 (s : astate) (k : nat) (x : Z * option sptr) : Prop :=
  exists g ag, usedX [] s g ag /\ prid (am_mem ag) = k /\
  match snd x with None => frameless ag /\ am_sc ag = fst x | Some b => exists n, witn s b n g end.

Definition R5 (s : astate) (g : sptr) (x : Z * option sptr) : Prop :=
  exists ag, usedX [] s g ag /\ am_sc ag = fst x /\
  match snd x with None => frameless ag | Some b => exists n, witn s b n g end.

Lemma regions_bound s (HW : WF s) (HS : SI s) kl : NoDup kl ->
  (forall k, In k kl -> exists rg, region_of s k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true) ->
  (length kl <= 48 + length (user_blocks s))%nat.
Proof.
  intros Hnd Hk.
  assert (L : (length kl <= length (mT4 (map fst (user_blocks s))))%nat).
  { apply (ac_count ac_kdec (R4 s)); [exact Hnd| |].
    - intros k Hin. destruct (Hk k Hin) as (rg & Hr & Kd & Lv).
      pose proof HS as (OM & EO & _). destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mp & Pk).
      destruct (frameless_dec ag) as [FL | Hx].
      + destruct (EO g ag U FL (ac_unres g)) as [_ C].
        exists (am_sc ag, None). split.
        * unfold mT4. apply in_app_iff. left. apply in_map_iff. exists (am_sc ag). split; [reflexivity | apply In_zseq; lia].
        * exists g, ag. split; [exact U|]. split; [exact Pk|]. split; [exact FL|reflexivity].
      + destruct (wit_ex s HW HS g ag U Hx) as (b & n & Hb & W).
        exists (0, Some b). split.
        * unfold mT4. apply in_app_iff. right. apply in_map_iff. exists b. split; [reflexivity | exact Hb].
        * exists g, ag. split; [exact U|]. split; [exact Pk|]. exists n. exact W.
    - intros k k' [c o] _ _ (g & a & U & Pk & H) (g' & a' & U' & Pk' & H'). subst k k'.
      destruct o as [b|]; cbn [fst snd] in H, H'.
      + destruct H as (n & W), H' as (n' & W').
        rewrite (witn_prid s HW b n g a W U), (witn_prid s HW b n' g' a' W' U'). reflexivity.
      + destruct H as (FL & E), H' as (FL' & E'). pose proof HS as (_ & _ & EU & _).
        rewrite (EU g a g' a' U U' FL FL' (ac_unres g) (ac_unres g') ltac:(lia)) in U.
        rewrite (usedX_fun _ _ _ _ _ U U'). reflexivity. }
  unfold mT4 in L. rewrite length_app, !length_map, zseq48 in L. exact L.
Qed.

Theorem map_count_bound : forall s, WF s -> SI s -> map_count s <= nblocks s + 48.
Proof.
  intros s HW HS. unfold map_count, nblocks. rewrite mapc_count.
  enough (L : (length (filter (fun k => match nth_error (st_regions s) k with
    Some rg => rg_live rg && is_map rg | None => false end) (seq 0 (length (st_regions s))))
    <= 48 + length (user_blocks s))%nat) by lia.
  apply (regions_bound s HW HS).
  - apply NoDup_filter. apply seq_NoDup.
  - intros k Hk. apply filter_In in Hk as [_ Hk]. cbv beta in Hk.
    destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; [|discriminate].
    apply andb_true_iff in Hk as [Lv Mp]. exists rg. split; [exact Hr|]. split; [|exact Lv].
    unfold is_map in Mp. destruct (rg_kind rg); try discriminate; reflexivity.
Qed.

Theorem nused_bound : forall s, WF s -> SI s -> nused s <= 49 * nblocks s + 48.
Proof.
  intros s HW HS. unfold nused, nblocks.
  assert (L : (length (map fst (used_metas s)) <= length (mT5 (map fst (user_blocks s))))%nat).
  { apply (ac_count ac_kdec (R5 s)).
    - apply NoDup_used_metas_keys. exact (proj1 (inv_keys HW)).
    - intros g Hg. apply in_map_iff in Hg as ([g' ag] & E & Hin). cbn [fst] in E. subst g'.
      apply (used_metas_usedX s g ag HW) in Hin.
      destruct (frameless_dec ag) as [FL | Hx].
      + pose proof HS as (_ & EO & _). destruct (EO g ag Hin FL (ac_unres g)) as [_ C].
        exists (am_sc ag, None). split.
        * unfold mT5. apply in_app_iff. left. apply in_map_iff. exists (am_sc ag). split; [reflexivity | apply In_zseq; lia].
        * exists ag. split; [exact Hin|]. split; [reflexivity|exact FL].
      + destruct (wit_ex s HW HS g ag Hin Hx) as (b & n & Hb & W).
        exists (am_sc ag, Some b). split.
        * unfold mT5. apply in_app_iff. right. apply in_flat_map. exists (am_sc ag). split.
          -- apply in_app_iff. destruct (sc_range s HW g ag Hin) as [E|E];
             [right; rewrite E; left; reflexivity | left; apply In_zseq; lia].
          -- apply in_map_iff. exists b. split; [reflexivity | exact Hb].
        * exists ag. split; [exact Hin|]. split; [reflexivity|]. exists n. exact W.
    - intros g g' [c o] _ _ (a & U & E & H) (a' & U' & E' & H').
      destruct o as [b|]; cbn [fst snd] in E, E', H, H'.
      + destruct H as (n & W), H' as (n' & W').
        exact (wit_inj s HW b n n' g a g' a' W W' U U' ltac:(lia)).
      + pose proof HS as (_ & _ & EU & _).
        exact (EU g a g' a' U U' H H' (ac_unres g) (ac_unres g') ltac:(lia)). }
  unfold mT5 in L. rewrite length_map, length_app, length_map, flat_len, length_app, zseq48, length_map in L.
  cbn [length] in L. lia.
Qed.
