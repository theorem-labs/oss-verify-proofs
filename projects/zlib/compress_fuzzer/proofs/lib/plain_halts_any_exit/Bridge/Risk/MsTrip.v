(** * Bridge.Risk.MsTrip — match_start live range, RT side: the trip-level
    invariants, common part and deflate_fast (group R).

    [msi s]: [cfg_ok] of the geometry and [MsFill.fi] of the window state;
    it is [MsDefs.ms_inv] ([ms_inv_msi]).  The top-of-loop fill keeps it
    ([fill_msi]); [df_l1_facts] describes deflate_fast's state after the
    hash insert and the [longest_match] call; [df_body_msi] shows a whole
    deflate_fast trip keeps [msi] and [ms_fast_inv]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Chunk Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require Import MsKit MsFill MsDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition msi (s : DSt) : Prop := cfg_ok (d_cfg s) /\ fi (d_cfg s) (d_ls s).

Lemma ms_inv_msi : forall s, ms_inv s <-> msi s.
Proof.
  intros s. split.
  - intros [Hc Hw Hm Hz Hs Hl Hr Hi Hwm Hhm]. unfold msi, cfg_ok, fi.
    split; [repeat split; tauto | split; [exact Hc | repeat split; tauto]].
  - intros [(Hw & Hm & Hwm & Hhs & Hhm) (Hc & Hs & Hl & Hr & Hz & Hi)].
    constructor; first [assumption | exact Hc | split; assumption].
Qed.

Lemma LV_fields : forall a b, LV b = LV a ->
  ls_matchlen b = ls_matchlen a /\ ls_strstart b = ls_strstart a /\ ls_matchstart b = ls_matchstart a
  /\ ls_lookahead b = ls_lookahead a /\ ls_prevlen b = ls_prevlen a /\ ls_insert b = ls_insert a
  /\ ls_windowsize b = ls_windowsize a /\ ls_prevmatch b = ls_prevmatch a /\ ls_matchavail b = ls_matchavail a.
Proof.
  intros a b E. unfold LV in E. repeat (apply pair_equal_spec in E as [E ?]). repeat split; assumption.
Qed.

Lemma fi_frame : forall g l l',
  ls_head l' = ls_head l -> ls_prev l' = ls_prev l -> ls_strstart l' = ls_strstart l ->
  ls_lookahead l' = ls_lookahead l -> ls_insert l' = ls_insert l -> ls_windowsize l' = ls_windowsize l ->
  fi g l -> fi g l'.
Proof.
  intros g l l' H1 H2 H3 H4 H5 H6 (C & A & B & D & E & F). unfold fi. rewrite H3, H4, H5, H6.
  split; [apply (chain_frame g g l l'); try reflexivity; assumption | auto].
Qed.

(** The [prev] half survives an insert at any position. *)
Lemma insert_prev : forall g str l b, cfg_ok g -> chain_below g l b ->
  prev_below g (snd (insert_string g str l)) b.
Proof.
  intros g str l b Hc [Hh Hp]. unfold insert_string, prev_below. cbv zeta. cbn [fst snd].
  set (h := update_hash g (ls_insh l) (ls_window l (str + MIN_MATCH - 1))).
  assert (Hr : 0 <= h < dg_hash_size g) by (apply hash_range; exact Hc).
  destruct (Hh h Hr) as (Hm0 & Hm1).
  intros i Hi. cbn [ls_prev setL_head setL_prev setL_insh]. unfold zset.
  destruct (Z.eqb_spec i (Z.land str (dg_w_mask g))); [split; assumption | exact (Hp i Hi)].
Qed.

Lemma lm_fst_le : forall g l c, fst (longest_match g l c) <= ls_lookahead l.
Proof.
  intros g l c. unfold longest_match. cbv zeta.
  match goal with |- context [lm_loop ?f ?x ?st] => destruct (lm_loop f x st) as [m1 m2 m3 m4 m5 m6] end.
  cbn [fst m_best]. destruct (Z.leb_spec m2 (ls_lookahead l)); lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* fill, flush                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma fill_msi : forall s, msi s ->
  msi (ds_fill s) /\ fw_same (d_ls s) (d_ls (ds_fill s)) /\ d_cfg (ds_fill s) = d_cfg s.
Proof.
  intros s [Hc Hf]. unfold ds_fill, fill_if. destruct (ds_need s).
  - pose proof (fill_window_inv (d_cfg s) (d_wrap s) (d_ls s) (d_strm s) Hc Hf) as F. cbv zeta in F |- *.
    destruct F as [F S]. cbn [d_ls d_cfg setD_strm setD_ls]. split; [split; assumption|]. split; [exact S | reflexivity].
  - split; [split; assumption|]. split; [apply fw_same_refl | reflexivity].
Qed.

Lemma flush_block_only_ls : forall last s,
  d_ls (flush_block_only last s) = setL_blockstart (ls_strstart (d_ls s)) (d_ls s)
  /\ d_cfg (flush_block_only last s) = d_cfg s.
Proof. intros. unfold flush_block_only, flush_pending. cbv zeta. destruct (_ =? 0); split; reflexivity. Qed.

Lemma flush_block_ls : forall last s,
  d_ls (snd (flush_block last s)) = setL_blockstart (ls_strstart (d_ls s)) (d_ls s)
  /\ d_cfg (snd (flush_block last s)) = d_cfg s.
Proof. intros. unfold flush_block. cbv zeta. destruct (_ =? 0); cbn [snd]; apply flush_block_only_ls. Qed.

Lemma step_fb : forall s,
  step_state (match flush_block 0 s with (Some bs, s4) => DsRet bs s4 | (None, s4) => DsCont s4 end)
  = snd (flush_block 0 s).
Proof. intros s. destruct (flush_block 0 s) as [[bs|] s4]; reflexivity. Qed.

(** What a trip must re-establish: [msi] and a predicate [Q] on the window
    state that a flush leaves alone. *)
Definition fb_inv (Q : DSt -> Prop) : Prop :=
  forall s s', d_cfg s' = d_cfg s -> ls_matchlen (d_ls s') = ls_matchlen (d_ls s)
  -> ls_prevlen (d_ls s') = ls_prevlen (d_ls s) -> ls_lookahead (d_ls s') = ls_lookahead (d_ls s)
  -> ls_strstart (d_ls s') = ls_strstart (d_ls s) -> ls_matchstart (d_ls s') = ls_matchstart (d_ls s)
  -> Q s -> Q s'.

Lemma flush_keeps : forall (Q : DSt -> Prop) s, fb_inv Q -> msi s -> Q s ->
  msi (snd (flush_block 0 s)) /\ Q (snd (flush_block 0 s)).
Proof.
  intros Q s HQ [Hc Hf] Hq. destruct (flush_block_ls 0 s) as [EL EC].
  split.
  - unfold msi. rewrite EC, EL. split; [exact Hc|]. apply (fi_frame _ (d_ls s)); try reflexivity. exact Hf.
  - apply (HQ s); try rewrite EL; try reflexivity; [exact EC | exact Hq].
Qed.

Lemma end_keeps : forall (Q : DSt -> Prop) (b : bool) s3, fb_inv Q -> msi s3 -> Q s3 ->
  msi (step_state (if b then match flush_block 0 s3 with (Some bs, s4) => DsRet bs s4 | (None, s4) => DsCont s4 end
                   else DsCont s3))
  /\ Q (step_state (if b then match flush_block 0 s3 with (Some bs, s4) => DsRet bs s4 | (None, s4) => DsCont s4 end
                   else DsCont s3)).
Proof. intros Q b s3 HQ Hm Hq. destruct b; [rewrite step_fb; apply flush_keeps | split]; assumption. Qed.

Lemma fast_fb : fb_inv ms_fast_inv.
Proof. intros s s' _ E1 E2 _ _ _ [A B]. unfold ms_fast_inv. rewrite E1, E2. split; assumption. Qed.

(* ------------------------------------------------------------------------- *)
(* the insert loops                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma dfi_rt : forall f g n l, cfg_ok g -> chain_below g l (ls_strstart l + 1) -> 1 <= n -> (Z.to_nat n <= f)%nat ->
  0 <= ls_strstart l -> ls_strstart l + n < 65536 ->
  let l' := df_insert f g n l in
  chain_below g l' (ls_strstart l' + 1) /\ ls_strstart l' = ls_strstart l + n
  /\ ls_lookahead l' = ls_lookahead l /\ ls_insert l' = ls_insert l /\ ls_windowsize l' = ls_windowsize l
  /\ ls_matchlen l' = ls_matchlen l /\ ls_prevlen l' = ls_prevlen l /\ ls_matchstart l' = ls_matchstart l.
Proof.
  induction f as [|f IH]; intros g n l Hc Hch Hn Hf Hs H64 l'; subst l'; [lia|].
  cbn [df_insert]. cbv zeta.
  set (l1 := setL_strstart (ls_strstart l + 1) l).
  assert (C1 : chain_below g l1 (ls_strstart l1)) by (apply (chain_frame g g l l1); reflexivity || exact Hch).
  assert (S1 : ls_strstart l1 = ls_strstart l + 1) by reflexivity.
  assert (V1 : LV l1 = LV (setL_strstart (ls_strstart l + 1) l)) by reflexivity.
  clearbody l1.
  destruct (insert_chain g (ls_strstart l1) l1 (ls_strstart l1) Hc C1 ltac:(lia)) as [C2 _].
  pose proof (LV_insert g (ls_strstart l1) l1) as EV.
  set (l2 := snd (insert_string g (ls_strstart l1) l1)) in *. clearbody l2.
  rewrite V1 in EV. destruct (LV_fields _ _ EV) as (M2 & S2 & MS2 & L2 & P2 & I2 & W2 & _).
  cbn [ls_matchlen ls_strstart ls_matchstart ls_lookahead ls_prevlen ls_insert ls_windowsize setL_strstart] in *.
  rewrite Z.max_r in C2 by lia.
  destruct (Z.eqb_spec (n - 1) 0) as [N0|N0].
  - rewrite S2. rewrite S1 in C2. split; [exact C2|]. repeat split; lia.
  - assert (C2' : chain_below g l2 (ls_strstart l2 + 1)) by (rewrite S2; rewrite S1 in C2; exact C2).
    destruct (IH g (n - 1) l2 Hc C2' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (C3 & S3 & L3 & I3 & W3 & M3 & P3 & MS3).
    split; [exact C3|]. repeat split; lia.
Qed.

Lemma df_insert_prevlen : forall f g n l, ls_prevlen (df_insert f g n l) = ls_prevlen l.
Proof.
  induction f as [|f IH]; intros g n l; [reflexivity|]. cbn [df_insert]. cbv zeta.
  destruct (_ =? 0); [reflexivity | rewrite IH; reflexivity].
Qed.

(* ------------------------------------------------------------------------- *)
(* deflate_fast                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma df_l1_facts : forall p0, msi p0 ->
  chain_below (d_cfg p0) (df_l1 p0) (ls_strstart (d_ls p0) + 1)
  /\ ls_strstart (df_l1 p0) = ls_strstart (d_ls p0) /\ ls_lookahead (df_l1 p0) = ls_lookahead (d_ls p0)
  /\ ls_insert (df_l1 p0) = ls_insert (d_ls p0) /\ ls_windowsize (df_l1 p0) = ls_windowsize (d_ls p0)
  /\ ls_prevlen (df_l1 p0) = ls_prevlen (d_ls p0)
  /\ ((ls_matchlen (df_l1 p0) = ls_matchlen (d_ls p0) /\ ls_matchstart (df_l1 p0) = ls_matchstart (d_ls p0))
      \/ (ls_matchlen (df_l1 p0) <= ls_lookahead (d_ls p0)
          /\ (ls_prevlen (d_ls p0) < ls_matchlen (df_l1 p0) ->
              1 <= ls_strstart (d_ls p0) - ls_matchstart (df_l1 p0) <= dg_max_dist (d_cfg p0)))).
Proof.
  intros p0 [Hc Hf]. pose proof Hf as (Hch & Hs & Hl & Hr & Hw & Hi). pose proof Hc as (Hws & Hmd & Hwm & Hhs & Hhm).
  unfold df_l1. cbv zeta.
  set (g := d_cfg p0) in *. set (l := d_ls p0) in *. clearbody g l.
  destruct (Z.leb_spec MIN_MATCH (ls_lookahead l)) as [H3|H3].
  - destruct (insert_chain g (ls_strstart l) l (ls_strstart l) Hc Hch ltac:(unfold MIN_MATCH in H3; lia)) as [C1 [M0 M1]].
    pose proof (insert_prev g (ls_strstart l) l (ls_strstart l) Hc Hch) as P1.
    pose proof (LV_insert g (ls_strstart l) l) as EV.
    set (mh := fst (insert_string g (ls_strstart l) l)) in *.
    set (l0 := snd (insert_string g (ls_strstart l) l)) in *. clearbody mh l0.
    destruct (LV_fields _ _ EV) as (ML0 & S0 & MS0 & L0 & PL0 & I0 & W0 & _).
    rewrite Z.max_r in C1 by lia.
    destruct (negb (mh =? NIL) && (ls_strstart l0 - mh <=? dg_max_dist g)) eqn:E.
    + apply andb_true_iff in E as [E1 E2]. apply negb_true_iff, Z.eqb_neq in E1. apply Z.leb_le in E2.
      assert (P1' : prev_below g l0 (ls_strstart l0)) by (rewrite S0; exact P1).
      pose proof (lm_live g l0 mh Hwm ltac:(lia) P1' ltac:(destruct M1; unfold NIL in *; lia) E2) as LL. cbv zeta in LL.
      pose proof (lm_fst_le g l0 mh) as LF.
      cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_prevlen ls_matchlen ls_matchstart setL_matchstart setL_matchlen].
      split; [apply (chain_frame g g l0); try reflexivity; exact C1|].
      repeat split; try lia. all: right; split; [lia|]; intros Hpl; rewrite S0 in LL; apply LL; lia.
    + split; [exact C1|]. repeat split; try lia. all: left; split; lia.
  - cbn [fst snd]. change (negb (NIL =? NIL)) with false. cbn [andb].
    split; [apply (chain_mono g l (ls_strstart l)); [lia | exact Hch]|]. repeat split; try reflexivity. left; split; reflexivity.
Qed.

Lemma df_body_eq : forall flush p0,
  df_body flush p0 =
  (let g := d_cfg p0 in
   let l1 := df_l1 p0 in
   let s2 := setD_ls l1 p0 in
   if Z.leb MIN_MATCH (ls_matchlen l1) then
     let tt := tr_tally_dist (ls_strstart l1 - ls_matchstart l1) (ls_matchlen l1 - MIN_MATCH) (dg_sym_end g) (d_ts s2) in
     let l2 := setL_lookahead (ls_lookahead l1 - ls_matchlen l1) l1 in
     let l4 :=
       if (Z.leb (ls_matchlen l2) (dg_max_lazy_match g)) && (Z.leb MIN_MATCH (ls_lookahead l2)) then
         let l3 := setL_matchlen (ls_matchlen l2 - 1) l2 in
         let l3b := df_insert (Z.to_nat (ls_matchlen l3) + 1) g (ls_matchlen l3) l3 in
         setL_strstart (ls_strstart l3b + 1) (setL_matchlen 0 l3b)
       else
         let l3 := setL_matchlen 0 (setL_strstart (ls_strstart l2 + ls_matchlen l2) l2) in
         let h0 := ls_window l3 (ls_strstart l3) in
         setL_insh (update_hash g h0 (ls_window l3 (ls_strstart l3 + 1))) l3 in
     let s3 := setD_ls l4 (setD_ts (snd tt) s2) in
     if fst tt then
       match flush_block 0 s3 with
       | (Some bs, s4) => DsRet bs s4
       | (None, s4) => DsCont s4
       end
     else DsCont s3
   else
     let tt := tr_tally_lit (ls_window l1 (ls_strstart l1)) (dg_sym_end g) (d_ts s2) in
     let s3 := setD_ls (setL_strstart (ls_strstart l1 + 1) (setL_lookahead (ls_lookahead l1 - 1) l1))
                       (setD_ts (snd tt) s2) in
     if fst tt then
       match flush_block 0 s3 with
       | (Some bs, s4) => DsRet bs s4
       | (None, s4) => DsCont s4
       end
     else DsCont s3).
Proof. reflexivity. Qed.

Lemma df_body_msi : forall flush p0, msi p0 -> ms_fast_inv p0 -> 1 <= ls_lookahead (d_ls p0) ->
  msi (step_state (df_body flush p0)) /\ ms_fast_inv (step_state (df_body flush p0)).
Proof.
  intros flush p0 Hm Hfi Hl1. pose proof Hm as [Hc Hf]. pose proof Hf as (Hch & Hs & Hl & Hr & Hw & Hi).
  pose proof Hc as (Hws & Hmd & Hwm & Hhs & Hhm). destruct Hfi as [Fm Fp].
  destruct (df_l1_facts p0 Hm) as (C1 & S1 & L1 & I1 & W1 & P1 & D1).
  rewrite df_body_eq. cbv zeta.
  set (l1 := df_l1 p0) in *. clearbody l1.
  unfold MIN_MATCH in *.
  destruct (Z.leb_spec 3 (ls_matchlen l1)) as [Hd|Hd].
  - (* a match *)
    assert (Hml : ls_matchlen l1 <= ls_lookahead (d_ls p0)) by (destruct D1 as [[X _]|[X _]]; [lia | exact X]).
    apply end_keeps; [exact fast_fb | |].
    + unfold msi. cbn [d_cfg d_ls setD_ls setD_ts]. split; [exact Hc|].
      destruct (_ && _).
      * set (l3 := setL_matchlen _ (setL_lookahead _ l1)).
        assert (C3 : chain_below (d_cfg p0) l3 (ls_strstart l3 + 1))
          by (subst l3; apply (chain_frame (d_cfg p0) (d_cfg p0) l1); try reflexivity; rewrite <- S1 in C1; exact C1).
        destruct (dfi_rt (Z.to_nat (ls_matchlen l3) + 1) (d_cfg p0) (ls_matchlen l3) l3 Hc C3) as (C4 & S4 & L4 & I4 & W4 & _).
        { subst l3. cbn. lia. }
        { lia. }
        { subst l3. cbn. lia. }
        { subst l3. cbn. lia. }
        subst l3. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_matchlen setL_matchlen setL_lookahead setL_strstart] in *.
        unfold fi. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_head ls_prev setL_strstart setL_matchlen].
        set (X := df_insert (Z.to_nat _ + 1) (d_cfg p0) _ _) in *.
        split; [exact (chain_frame (d_cfg p0) (d_cfg p0) X _ _ eq_refl eq_refl eq_refl eq_refl C4)|].
        repeat split; lia.
      * unfold fi. cbn [ls_strstart ls_lookahead ls_insert ls_windowsize ls_head ls_prev ls_matchlen setL_insh setL_matchlen setL_strstart setL_lookahead].
        split; [apply (chain_mono (d_cfg p0) l1 (ls_strstart (d_ls p0) + 1)); [lia | exact C1]|].
        repeat split; lia.
    + unfold ms_fast_inv, MIN_MATCH. cbn [d_ls setD_ls setD_ts].
      destruct (_ && _); cbn [ls_matchlen ls_prevlen setL_insh setL_matchlen setL_strstart setL_lookahead];
        rewrite ?df_insert_prevlen; cbn [ls_prevlen setL_matchlen setL_lookahead]; split; lia.
  - (* a literal *)
    apply end_keeps; [exact fast_fb | |].
    + unfold msi, fi. cbn [d_cfg d_ls setD_ls setD_ts ls_strstart ls_lookahead ls_insert ls_windowsize ls_head ls_prev setL_strstart setL_lookahead].
      split; [exact Hc|]. split; [rewrite S1; apply (chain_frame (d_cfg p0) (d_cfg p0) l1); try reflexivity; exact C1|]. repeat split; lia.
    + unfold ms_fast_inv, MIN_MATCH. cbn [d_ls setD_ls setD_ts ls_matchlen ls_prevlen setL_strstart setL_lookahead]. split; lia.
Qed.
