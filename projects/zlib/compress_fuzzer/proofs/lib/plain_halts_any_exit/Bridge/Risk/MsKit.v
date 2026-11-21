(** * Bridge.Risk.MsKit — match_start live range, RT side: the hash-chain
    invariant and [longest_match] (group R).

    RT keeps [head]/[prev] as total arrays of positions ([u16]), NIL = 0.
    [chain_below g l b]: every [head] slot of the hash table and every
    [prev] slot of the window is NIL or a position below [b] (all
    non-negative).  The invariant RiskIface names [ms_chain_ok] is
    [chain_below g l (ls_strstart l)].  Here: monotonicity, the effect of
    [insert_string] (adds one position) and of [slide_hash] (shifts every
    bound down by [w_size]), and [longest_match]: when it improves on
    [prev_length] the start it reports is one of the chain positions it
    walked, all in [[strstart - max_dist, strstart - 1]]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Chunk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require FillWinModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** The configuration facts every deflateInit2 geometry has. *)
Definition cfg_ok (g : DeflGeom) : Prop :=
  512 <= dg_w_size g <= 32768 /\ dg_max_dist g = dg_w_size g - MIN_LOOKAHEAD
  /\ dg_w_mask g = dg_w_size g - 1 /\ 1 <= dg_hash_size g /\ dg_hash_mask g = dg_hash_size g - 1.

Definition head_below (g : DeflGeom) (l : LSt) (b : Z) : Prop :=
  forall i, 0 <= i < dg_hash_size g -> 0 <= ls_head l i /\ (ls_head l i = NIL \/ ls_head l i < b).

Definition prev_below (g : DeflGeom) (l : LSt) (b : Z) : Prop :=
  forall i, 0 <= i < dg_w_size g -> 0 <= ls_prev l i /\ (ls_prev l i = NIL \/ ls_prev l i < b).

Definition chain_below (g : DeflGeom) (l : LSt) (b : Z) : Prop := head_below g l b /\ prev_below g l b.

Lemma below_mono : forall (a : zarr) n b b', b <= b' ->
  (forall i, 0 <= i < n -> 0 <= a i /\ (a i = NIL \/ a i < b)) ->
  (forall i, 0 <= i < n -> 0 <= a i /\ (a i = NIL \/ a i < b')).
Proof. intros a n b b' Hb H i Hi. destruct (H i Hi) as [A [B|B]]; split; auto. right; lia. Qed.

Lemma chain_mono : forall g l b b', b <= b' -> chain_below g l b -> chain_below g l b'.
Proof. intros g l b b' Hb [H1 H2]. split; [exact (below_mono _ _ _ _ Hb H1) | exact (below_mono _ _ _ _ Hb H2)]. Qed.

Lemma chain_frame : forall g g' l l' b,
  dg_hash_size g' = dg_hash_size g -> dg_w_size g' = dg_w_size g ->
  ls_head l' = ls_head l -> ls_prev l' = ls_prev l -> chain_below g l b -> chain_below g' l' b.
Proof. intros g g' l l' b E1 E2 E3 E4 [H1 H2]. unfold chain_below, head_below, prev_below. rewrite E1, E2, E3, E4. split; assumption. Qed.

Lemma hash_range : forall g h c, cfg_ok g -> 0 <= update_hash g h c < dg_hash_size g.
Proof.
  intros g h c (_ & _ & _ & Hs & Hm). unfold update_hash.
  pose proof (FillWinModel.land_mask_range (Z.lxor (Z.shiftl h (dg_hash_shift g)) c) (dg_hash_mask g) ltac:(lia)). lia.
Qed.

Lemma u16_id : forall v, 0 <= v < 65536 -> u16 v = v.
Proof. intros v H. unfold u16. apply Z.mod_small. exact H. Qed.

(** Everything but [head], [prev] and [ins_h]. *)
Definition LV (l : LSt) :=
  (ls_window l, ls_blockstart l, ls_matchlen l, ls_prevmatch l, ls_matchavail l, ls_strstart l,
   ls_matchstart l, ls_lookahead l, ls_prevlen l, ls_insert l, ls_highwater l, ls_windowsize l).

Lemma LV_insert : forall g str l, LV (snd (insert_string g str l)) = LV l.
Proof. reflexivity. Qed.

Lemma insert_chain : forall g str l b, cfg_ok g -> chain_below g l b -> 0 <= str < 65536 ->
  chain_below g (snd (insert_string g str l)) (Z.max b (str + 1))
  /\ 0 <= fst (insert_string g str l) /\ (fst (insert_string g str l) = NIL \/ fst (insert_string g str l) < b).
Proof.
  intros g str l b Hc [Hh Hp] Hs. unfold insert_string. cbv zeta. cbn [fst snd].
  set (h := update_hash g (ls_insh l) (ls_window l (str + MIN_MATCH - 1))).
  assert (Hr : 0 <= h < dg_hash_size g) by (apply hash_range; exact Hc).
  destruct (Hh h Hr) as (Hm0 & Hm1).
  split; [split|].
  - intros i Hi. cbn [ls_head setL_head setL_prev setL_insh]. unfold zset.
    destruct (Z.eqb_spec i h).
    + rewrite u16_id by lia. split; [lia | right; lia].
    + destruct (Hh i Hi) as (A & B). split; [exact A|]. destruct B; [left; assumption | right; lia].
  - intros i Hi. cbn [ls_prev setL_head setL_prev setL_insh]. unfold zset.
    destruct (Z.eqb_spec i (Z.land str (dg_w_mask g))).
    + split; [exact Hm0|]. destruct Hm1; [left; assumption | right; lia].
    + destruct (Hp i Hi) as (A & B). split; [exact A|]. destruct B; [left; assumption | right; lia].
  - split; [exact Hm0|]. exact Hm1.
Qed.

Lemma slide_range_below : forall (a : zarr) n ws b, 1 <= ws -> ws <= b <= 65536 ->
  (forall i, 0 <= i < n -> 0 <= a i /\ (a i = NIL \/ a i < b)) ->
  (forall i, 0 <= i < n -> 0 <= slide_range n ws a i /\ (slide_range n ws a i = NIL \/ slide_range n ws a i < b - ws)).
Proof.
  intros a n ws b Hw Hb H i Hi. unfold slide_range.
  replace ((0 <=? i) && (i <? n)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  destruct (H i Hi) as (A & B). unfold slide_one, NIL in *.
  destruct (Z.leb_spec ws (a i)).
  - rewrite u16_id by lia. split; [lia | right; lia].
  - rewrite u16_id by lia. split; [lia | left; reflexivity].
Qed.

Lemma slide_chain : forall g l b, cfg_ok g -> dg_w_size g <= b <= 65536 -> chain_below g l b ->
  chain_below g (slide_hash g l) (b - dg_w_size g).
Proof.
  intros g l b Hc Hb [Hh Hp]. pose proof Hc as (Hw & _). unfold slide_hash, chain_below, head_below, prev_below. cbv zeta.
  cbn [ls_head ls_prev setL_head setL_prev]. split.
  - apply slide_range_below; [lia | lia | exact Hh].
  - apply slide_range_below; [lia | lia | exact Hp].
Qed.

Lemma LV_slide_hash : forall g l, LV (slide_hash g l) = LV l.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* longest_match                                                             *)
(* ------------------------------------------------------------------------- *)

Section LM.
Variables (g : DeflGeom) (l : LSt) (c : LmCtx) (bl0 : Z).
Hypothesis Hwm : dg_w_mask g = dg_w_size g - 1.
Hypothesis Hws : 1 <= dg_w_size g.
Hypothesis Hp : prev_below g l (ls_strstart l).
Hypothesis Hsc : x_scan c = ls_strstart l.
Hypothesis Hpv : x_prev c = ls_prev l.
Hypothesis Hmk : x_wmask c = dg_w_mask g.
Hypothesis Hlim : x_limit c = (if dg_max_dist g <? ls_strstart l then ls_strstart l - dg_max_dist g else NIL).

Definition live (x : Z) : Prop := 1 <= ls_strstart l - x <= dg_max_dist g.

Lemma lm_loop_live : forall f st, 1 <= m_cur st -> live (m_cur st) ->
  (bl0 < m_best st -> live (m_start st)) ->
  bl0 < m_best (lm_loop f c st) -> live (m_start (lm_loop f c st)).
Proof.
  induction f as [|f IH]; intros st Hc1 Hc2 Hs; [exact Hs|].
  cbn [lm_loop]. unfold lm_step. cbv zeta.
  assert (S1 : bl0 < m_best (lm_next c st) -> live (m_start (lm_next c st))).
  { unfold lm_next. destruct (lm_hit c st); cbn [m_best m_start]; [intros _; exact Hc2 | exact Hs]. }
  destruct (lm_hit c st && (x_nice c <=? lm_len c st)); [exact S1|].
  set (cm' := x_prev c (Z.land (m_cur st) (x_wmask c))).
  destruct ((x_limit c <? cm') && negb (m_chain (lm_next c st) - 1 =? 0)) eqn:E.
  - apply IH; cbn [m_cur m_best m_start]; [| | exact S1].
    + apply andb_true_iff in E as [E _]. apply Z.ltb_lt in E. revert E. rewrite Hlim.
      destruct (Z.ltb_spec (dg_max_dist g) (ls_strstart l)); unfold NIL; intros E; lia.
    + apply andb_true_iff in E as [E _]. apply Z.ltb_lt in E.
      assert (Hi : 0 <= Z.land (m_cur st) (x_wmask c) < dg_w_size g).
      { rewrite Hmk. pose proof (FillWinModel.land_mask_range (m_cur st) (dg_w_mask g) ltac:(lia)). lia. }
      destruct (Hp _ Hi) as (A & B). unfold cm' in E |- *. rewrite Hpv in E |- *. unfold live. revert E. rewrite Hlim.
      destruct B as [B|B]; unfold NIL in *;
        destruct (Z.ltb_spec (dg_max_dist g) (ls_strstart l)); intros E; lia.
  - cbn [m_best m_start]. exact S1.
Qed.
End LM.

(** [longest_match] reports a live start whenever it improves on
    [prev_length]. *)
Theorem lm_live : forall g l cur,
  dg_w_mask g = dg_w_size g - 1 -> 1 <= dg_w_size g ->
  prev_below g l (ls_strstart l) -> NIL < cur < ls_strstart l -> ls_strstart l - cur <= dg_max_dist g ->
  let r := longest_match g l cur in
  ls_prevlen l < fst r -> 1 <= ls_strstart l - snd r <= dg_max_dist g.
Proof.
  intros g l cur Hwm Hws Hp Hc Hd r. subst r. unfold longest_match. cbv zeta.
  match goal with |- context [lm_loop ?f ?c ?st0] =>
    pose proof (lm_loop_live g l c (ls_prevlen l) Hwm Hws Hp eq_refl eq_refl eq_refl f st0) as L;
    destruct (lm_loop f c st0) as [m1 m2 m3 m4 m5 m6] end.
  cbn [m_cur m_best m_start] in L. cbn [fst snd m_best m_start].
  unfold live in L. unfold NIL in Hc.
  destruct (Z.leb_spec m2 (ls_lookahead l)) as [Q|Q]; intros Hpl; apply L; lia.
Qed.
