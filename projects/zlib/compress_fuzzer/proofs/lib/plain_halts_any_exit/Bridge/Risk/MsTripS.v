(** * Bridge.Risk.MsTripS — match_start live range, RT side: deflate_slow's
    trip keeps [msi] and [ms_slow_inv] (group R). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Chunk Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require Import MsKit MsFill MsDefs MsTrip.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma slow_fb : fb_inv ms_slow_inv.
Proof.
  intros s s' EC E1 E2 E3 E4 E5 [A B]. unfold ms_slow_inv. rewrite EC, E1, E3, E4, E5. split; assumption.
Qed.

Lemma dsi_rt : forall f g mi l, cfg_ok g -> chain_below g l (ls_strstart l + 1) -> 1 <= ls_prevlen l ->
  (Z.to_nat (ls_prevlen l) <= f)%nat -> 0 <= ls_strstart l -> ls_strstart l + ls_prevlen l < 65536 ->
  let l' := ds_insert f g mi l in
  chain_below g l' (ls_strstart l' + 1) /\ ls_strstart l' = ls_strstart l + ls_prevlen l
  /\ ls_lookahead l' = ls_lookahead l /\ ls_insert l' = ls_insert l /\ ls_windowsize l' = ls_windowsize l
  /\ ls_matchlen l' = ls_matchlen l /\ ls_matchstart l' = ls_matchstart l.
Proof.
  induction f as [|f IH]; intros g mi l Hc Hch Hp Hf Hs H64 l'; subst l'; [lia|].
  cbn [ds_insert]. cbv zeta.
  set (l1 := setL_strstart (ls_strstart l + 1) l).
  assert (C1 : chain_below g l1 (ls_strstart l1)) by (apply (chain_frame g g l l1); reflexivity || exact Hch).
  assert (S1 : ls_strstart l1 = ls_strstart l + 1) by reflexivity.
  assert (V1 : LV l1 = LV (setL_strstart (ls_strstart l + 1) l)) by reflexivity.
  clearbody l1.
  set (l2 := if ls_strstart l1 <=? mi then snd (insert_string g (ls_strstart l1) l1) else l1).
  assert (E2 : chain_below g l2 (ls_strstart l1 + 1) /\ LV l2 = LV l1).
  { subst l2. destruct (_ <=? mi).
    - destruct (insert_chain g (ls_strstart l1) l1 (ls_strstart l1) Hc C1 ltac:(lia)) as [C _].
      rewrite Z.max_r in C by lia. split; [exact C | apply LV_insert].
    - split; [apply (chain_mono g l1 (ls_strstart l1)); [lia | exact C1] | reflexivity]. }
  clearbody l2. destruct E2 as [C2 EV]. rewrite V1 in EV.
  destruct (LV_fields _ _ EV) as (M2 & S2 & MS2 & L2 & P2 & I2 & W2 & _).
  cbn [ls_matchlen ls_strstart ls_matchstart ls_lookahead ls_prevlen ls_insert ls_windowsize setL_strstart] in *.
  cbn [ls_prevlen setL_prevlen].
  destruct (Z.eqb_spec (ls_prevlen l2 - 1) 0) as [Z0|NZ].
  - unfold fi. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_matchlen ls_matchstart setL_prevlen].
    split; [apply (chain_frame g g l2); try reflexivity; rewrite S2; rewrite S1 in C2; exact C2|].
    repeat split; lia.
  - set (l3 := setL_prevlen (ls_prevlen l2 - 1) l2).
    assert (C3 : chain_below g l3 (ls_strstart l3 + 1))
      by (subst l3; apply (chain_frame g g l2); try reflexivity; cbn [ls_strstart setL_prevlen]; rewrite S2; rewrite S1 in C2; exact C2).
    destruct (IH g mi l3 Hc C3) as (C4 & S4 & L4 & I4 & W4 & M4 & MS4).
    { subst l3. cbn. lia. }
    { subst l3. cbn. lia. }
    { subst l3. cbn. lia. }
    { subst l3. cbn. lia. }
    subst l3. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_matchlen ls_matchstart ls_prevlen setL_prevlen] in *.
    split; [exact C4|]. repeat split; lia.
Qed.

Lemma ds_l2_facts : forall p0, msi p0 ->
  chain_below (d_cfg p0) (ds_l2 p0) (ls_strstart (d_ls p0) + 1)
  /\ ls_strstart (ds_l2 p0) = ls_strstart (d_ls p0) /\ ls_lookahead (ds_l2 p0) = ls_lookahead (d_ls p0)
  /\ ls_insert (ds_l2 p0) = ls_insert (d_ls p0) /\ ls_windowsize (ds_l2 p0) = ls_windowsize (d_ls p0)
  /\ ls_prevlen (ds_l2 p0) = ls_matchlen (d_ls p0) /\ ls_prevmatch (ds_l2 p0) = ls_matchstart (d_ls p0)
  /\ ls_matchavail (ds_l2 p0) = ls_matchavail (d_ls p0)
  /\ (ls_matchlen (ds_l2 p0) = MIN_MATCH - 1
      \/ (ls_matchlen (ds_l2 p0) <= ls_lookahead (d_ls p0)
          /\ (ls_matchlen (d_ls p0) < ls_matchlen (ds_l2 p0) ->
              1 <= ls_strstart (d_ls p0) - ls_matchstart (ds_l2 p0) <= dg_max_dist (d_cfg p0)))).
Proof.
  intros p0 [Hc Hf]. pose proof Hf as (Hch & Hs & Hl & Hr & Hw & Hi). pose proof Hc as (Hws & Hmd & Hwm & Hhs & Hhm).
  unfold ds_l2. cbv zeta.
  set (g := d_cfg p0) in *. set (l := d_ls p0) in *. clearbody g l.
  assert (PH : exists mh l0,
             (if MIN_MATCH <=? ls_lookahead l then insert_string g (ls_strstart l) l else (NIL, l)) = (mh, l0)
             /\ chain_below g l0 (ls_strstart l + 1) /\ prev_below g l0 (ls_strstart l) /\ LV l0 = LV l
             /\ 0 <= mh /\ (mh = NIL \/ mh < ls_strstart l)).
  { destruct (Z.leb_spec MIN_MATCH (ls_lookahead l)) as [H3|H3].
    - destruct (insert_chain g (ls_strstart l) l (ls_strstart l) Hc Hch ltac:(unfold MIN_MATCH in H3; lia)) as [C1 [M0 M1]].
      pose proof (insert_prev g (ls_strstart l) l (ls_strstart l) Hc Hch) as P1.
      rewrite Z.max_r in C1 by lia.
      exists (fst (insert_string g (ls_strstart l) l)), (snd (insert_string g (ls_strstart l) l)).
      split; [destruct (insert_string g (ls_strstart l) l); reflexivity|].
      split; [exact C1|]. split; [exact P1|]. split; [apply LV_insert|]. split; assumption.
    - exists NIL, l. split; [reflexivity|]. split; [apply (chain_mono g l (ls_strstart l)); [lia | exact Hch]|].
      split; [exact (proj2 Hch)|]. split; [reflexivity|]. unfold NIL. split; [lia | left; reflexivity]. }
  destruct PH as (mh & l0 & E & C0 & P0 & EV & M0 & M1). rewrite E. cbn [fst snd].
  destruct (LV_fields _ _ EV) as (ML0 & S0 & MS0 & L0 & PL0 & I0 & W0 & PM0 & MA0).
  set (l1 := setL_matchlen (MIN_MATCH - 1) (setL_prevmatch (ls_matchstart l0) (setL_prevlen (ls_matchlen l0) l0))).
  assert (E1 : chain_below g l1 (ls_strstart l + 1) /\ prev_below g l1 (ls_strstart l1) /\ ls_strstart l1 = ls_strstart l
               /\ ls_lookahead l1 = ls_lookahead l /\ ls_insert l1 = ls_insert l /\ ls_windowsize l1 = ls_windowsize l
               /\ ls_prevlen l1 = ls_matchlen l /\ ls_prevmatch l1 = ls_matchstart l /\ ls_matchavail l1 = ls_matchavail l
               /\ ls_matchlen l1 = MIN_MATCH - 1).
  { subst l1. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_prevlen ls_prevmatch ls_matchavail ls_matchlen
                   setL_matchlen setL_prevmatch setL_prevlen].
    split; [apply (chain_frame g g l0); try reflexivity; exact C0|].
    split; [unfold prev_below in *; cbn [ls_prev ls_strstart setL_matchlen setL_prevmatch setL_prevlen]; rewrite S0; exact P0|].
    repeat split; congruence. }
  clearbody l1. destruct E1 as (C1 & P1 & S1 & L1 & I1 & W1 & PL1 & PM1 & MA1 & ML1).
  destruct (negb (mh =? NIL) && (ls_prevlen l1 <? dg_max_lazy_match g) && (ls_strstart l1 - mh <=? dg_max_dist g)) eqn:EC.
  - apply andb_true_iff in EC as [EC E3]. apply andb_true_iff in EC as [E1 _].
    apply negb_true_iff, Z.eqb_neq in E1. apply Z.leb_le in E3.
    pose proof (lm_live g l1 mh Hwm ltac:(lia) P1 ltac:(destruct M1; unfold NIL in *; lia) E3) as LL. cbv zeta in LL.
    pose proof (lm_fst_le g l1 mh) as LF.
    set (r := longest_match g l1 mh) in *. clearbody r.
    set (l1a := setL_matchstart (snd r) (setL_matchlen (fst r) l1)).
    assert (A : chain_below g l1a (ls_strstart l + 1) /\ ls_strstart l1a = ls_strstart l /\ ls_lookahead l1a = ls_lookahead l
                /\ ls_insert l1a = ls_insert l /\ ls_windowsize l1a = ls_windowsize l /\ ls_prevlen l1a = ls_matchlen l
                /\ ls_prevmatch l1a = ls_matchstart l /\ ls_matchavail l1a = ls_matchavail l
                /\ ls_matchlen l1a <= ls_lookahead l
                /\ (ls_matchlen l < ls_matchlen l1a -> 1 <= ls_strstart l - ls_matchstart l1a <= dg_max_dist g)).
    { subst l1a. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_prevlen ls_prevmatch ls_matchavail ls_matchlen ls_matchstart
                      setL_matchstart setL_matchlen].
      split; [apply (chain_frame g g l1); try reflexivity; exact C1|]. rewrite S1 in LL. repeat split; try congruence; try lia.
      all: intros Hlt; apply LL; lia. }
    clearbody l1a. destruct A as (CA & SA & LA & IA & WA & PLA & PMA & MAA & MLA & LVA).
    destruct (_ && _).
    + cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_prevlen ls_prevmatch ls_matchavail ls_matchlen setL_matchlen].
      split; [apply (chain_frame g g l1a); try reflexivity; exact CA|]. repeat split; try congruence. left; reflexivity.
    + split; [exact CA|]. repeat split; try congruence. right. split; [exact MLA | exact LVA].
  - split; [exact C1|]. repeat split; try congruence. left; exact ML1.
Qed.

Lemma ds_body_eq : forall flush p0,
  ds_body flush p0 =
  (let g := d_cfg p0 in
   let l2 := ds_l2 p0 in
   let s2 := setD_ls l2 p0 in
   if (Z.leb MIN_MATCH (ls_prevlen l2)) && (Z.leb (ls_matchlen l2) (ls_prevlen l2)) then
     let max_insert := ls_strstart l2 + ls_lookahead l2 - MIN_MATCH in
     let tt := tr_tally_dist (ls_strstart l2 - 1 - ls_prevmatch l2) (ls_prevlen l2 - MIN_MATCH) (dg_sym_end g) (d_ts s2) in
     let bflush := fst tt in
     let l3 := setL_prevlen (ls_prevlen l2 - 2) (setL_lookahead (ls_lookahead l2 - (ls_prevlen l2 - 1)) l2) in
     let l4 := ds_insert (Z.to_nat (ls_prevlen l3) + 1) g max_insert l3 in
     let l5 := setL_strstart (ls_strstart l4 + 1) (setL_matchlen (MIN_MATCH - 1) (setL_matchavail 0 l4)) in
     let s3 := setD_ls l5 (setD_ts (snd tt) s2) in
     if bflush then
       match flush_block 0 s3 with
       | (Some bs, s4) => DsRet bs s4
       | (None, s4) => DsCont s4
       end
     else DsCont s3
   else if negb (Z.eqb (ls_matchavail l2) 0) then
     let tt := tr_tally_lit (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g) (d_ts s2) in
     let s3 := setD_ts (snd tt) s2 in
     let s4 := if fst tt then flush_block_only 0 s3 else s3 in
     let s5 := setD_ls (setL_lookahead (ls_lookahead (d_ls s4) - 1)
                         (setL_strstart (ls_strstart (d_ls s4) + 1) (d_ls s4))) s4 in
     if Z.eqb (zs_availout (d_strm s5)) 0 then DsRet NeedMore s5 else DsCont s5
   else
     DsCont (setD_ls (setL_lookahead (ls_lookahead l2 - 1)
                       (setL_strstart (ls_strstart l2 + 1)
                         (setL_matchavail 1 l2))) s2)).
Proof. reflexivity. Qed.

(** The two non-emitting branches end by advancing one byte from the trip's
    state (after a possible flush of the literal). *)
Lemma slow_tail : forall p0 l2 s, msi p0 -> 1 <= ls_lookahead (d_ls p0) ->
  chain_below (d_cfg p0) l2 (ls_strstart (d_ls p0) + 1) -> ls_strstart l2 = ls_strstart (d_ls p0) ->
  ls_lookahead l2 = ls_lookahead (d_ls p0) -> ls_insert l2 = ls_insert (d_ls p0) ->
  ls_windowsize l2 = ls_windowsize (d_ls p0) ->
  (ls_matchlen l2 = 2 \/ (ls_matchlen l2 <= ls_lookahead (d_ls p0)
                          /\ (ls_prevlen l2 < ls_matchlen l2 -> 1 <= ls_strstart (d_ls p0) - ls_matchstart l2 <= dg_max_dist (d_cfg p0)))) ->
  (3 <= ls_matchlen l2 -> ls_prevlen l2 < ls_matchlen l2) ->
  d_cfg s = d_cfg p0 ->
  (d_ls s = l2 \/ d_ls s = setL_blockstart (ls_strstart l2) l2 \/ d_ls s = setL_matchavail 1 l2) ->
  let s5 := setD_ls (setL_lookahead (ls_lookahead (d_ls s) - 1) (setL_strstart (ls_strstart (d_ls s) + 1) (d_ls s))) s in
  msi s5 /\ ms_slow_inv s5.
Proof.
  intros p0 l2 s [Hc Hf] Hl1 C2 S2 L2 I2 W2 D2 N2 G E s5. subst s5.
  pose proof Hf as (Hch & Hs & Hl & Hr & Hw & Hi).
  unfold msi, fi, ms_slow_inv, MIN_MATCH. cbn [d_cfg d_ls setD_ls ls_strstart ls_lookahead ls_insert ls_windowsize ls_head ls_prev
                                                ls_matchlen ls_matchstart setL_lookahead setL_strstart]. rewrite G.
  destruct E as [E|[E|E]]; rewrite E; cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_head ls_prev ls_matchlen ls_matchstart
                                           setL_blockstart setL_matchavail];
    (split; [split; [exact Hc | split; [rewrite S2; apply (chain_frame (d_cfg p0) (d_cfg p0) l2); try reflexivity; exact C2 | repeat split; lia]]|]);
    (destruct D2 as [D2|[D2a D2b]]; [split; [left; lia | intros; lia] | split; [right; lia | intros X; specialize (D2b (N2 X)); lia]]).
Qed.

Lemma ds_body_msi : forall flush p0, msi p0 -> ms_slow_inv p0 -> 1 <= ls_lookahead (d_ls p0) ->
  msi (step_state (ds_body flush p0)) /\ ms_slow_inv (step_state (ds_body flush p0)).
Proof.
  intros flush p0 Hm Hsi Hl1. pose proof Hm as [Hc Hf]. pose proof Hf as (Hch & Hs & Hl & Hr & Hw & Hi).
  pose proof Hc as (Hws & Hmd & Hwm & Hhs & Hhm). destruct Hsi as [Sm Sl].
  destruct (ds_l2_facts p0 Hm) as (C2 & S2 & L2 & I2 & W2 & PL2 & PM2 & MA2 & D2).
  rewrite ds_body_eq. cbv zeta.
  set (l2 := ds_l2 p0) in *. clearbody l2.
  rewrite <- PL2 in D2.
  unfold MIN_MATCH in *. unfold MIN_LOOKAHEAD, MAX_MATCH in Hmd.
  destruct ((3 <=? ls_prevlen l2) && (ls_matchlen l2 <=? ls_prevlen l2)) eqn:EB.
  - (* the previous match is emitted *)
    apply andb_true_iff in EB as [Hp3 Hle]. apply Z.leb_le in Hp3. apply Z.leb_le in Hle.
    assert (Hpl : ls_prevlen l2 <= ls_lookahead (d_ls p0) + 1) by (destruct Sm; lia).
    apply end_keeps; [exact slow_fb | |].
    + set (l3 := setL_prevlen _ (setL_lookahead _ l2)).
      assert (C3 : chain_below (d_cfg p0) l3 (ls_strstart l3 + 1))
        by (subst l3; apply (chain_frame (d_cfg p0) (d_cfg p0) l2); try reflexivity; cbn; rewrite S2; exact C2).
      destruct (dsi_rt (Z.to_nat (ls_prevlen l3) + 1) (d_cfg p0) (ls_strstart l2 + ls_lookahead l2 - 3) l3 Hc C3)
        as (C4 & S4 & L4 & I4 & W4 & _).
      { subst l3. cbn. lia. }
      { lia. }
      { subst l3. cbn. lia. }
      { subst l3. cbn. lia. }
      subst l3. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_prevlen setL_prevlen setL_lookahead] in *.
      unfold msi, fi. cbn [d_cfg d_ls setD_ls setD_ts ls_strstart ls_lookahead ls_insert ls_windowsize ls_head ls_prev
                           setL_strstart setL_matchlen setL_matchavail].
      set (X := ds_insert (Z.to_nat _ + 1) (d_cfg p0) _ _) in *.
      split; [exact Hc|]. split; [exact (chain_frame (d_cfg p0) (d_cfg p0) X _ _ eq_refl eq_refl eq_refl eq_refl C4)|].
      repeat split; lia.
    + unfold ms_slow_inv, MIN_MATCH. cbn [d_ls setD_ls setD_ts ls_matchlen setL_strstart setL_matchlen setL_matchavail].
      split; [left; lia | intros X; lia].
  - assert (N2 : 3 <= ls_matchlen l2 -> ls_prevlen l2 < ls_matchlen l2).
    { intros H3. apply andb_false_iff in EB as [EB|EB]; [apply Z.leb_gt in EB | apply Z.leb_gt in EB]; lia. }
    destruct (negb (ls_matchavail l2 =? 0)).
    + (* literal of the previous position *)
      match goal with |- context [if fst ?t then flush_block_only 0 ?x else ?y] =>
        assert (E4 : d_ls (if fst t then flush_block_only 0 x else y) = l2
                     \/ d_ls (if fst t then flush_block_only 0 x else y) = setL_blockstart (ls_strstart l2) l2
                     \/ d_ls (if fst t then flush_block_only 0 x else y) = setL_matchavail 1 l2)
          by (destruct (fst t); [right; left; rewrite (proj1 (flush_block_only_ls 0 x)); reflexivity | left; reflexivity]);
        assert (G4 : d_cfg (if fst t then flush_block_only 0 x else y) = d_cfg p0)
          by (destruct (fst t); [rewrite (proj2 (flush_block_only_ls 0 x)); reflexivity | reflexivity]);
        pose proof (slow_tail p0 l2 (if fst t then flush_block_only 0 x else y) Hm Hl1 C2 S2 L2 I2 W2 D2 N2 G4 E4) as K;
        set (s4 := if fst t then flush_block_only 0 x else y) in *
      end.
      cbv zeta in K. destruct (_ =? 0); exact K.
    + (* a new match becomes the pending one *)
      pose proof (slow_tail p0 l2 (setD_ls (setL_matchavail 1 l2) p0) Hm Hl1 C2 S2 L2 I2 W2 D2 N2 eq_refl
                    (or_intror (or_intror eq_refl))) as K.
      cbv zeta in K. exact K.
Qed.
