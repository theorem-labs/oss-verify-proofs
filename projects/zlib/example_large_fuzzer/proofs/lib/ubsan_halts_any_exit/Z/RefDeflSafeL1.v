(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition CHAINW (s : deflate_state) (BH BP : Z) (WS : Z -> Prop) : Prop :=
  (forall h, 0 <= h < ds_hash_size s ->
     arr_get (ds_head s) h = 0 \/ (1 <= arr_get (ds_head s) h <= BH /\ WS (Z.land (arr_get (ds_head s) h) (ds_w_mask s))))
  /\ (forall q, WS q ->
     0 <= q < ds_w_size s
     /\ (arr_get (ds_prev s) q = 0 \/ (1 <= arr_get (ds_prev s) q <= BP /\ WS (Z.land (arr_get (ds_prev s) q) (ds_w_mask s))))).

Definition CHAIN (s : deflate_state) (BH BP : Z) : Prop := exists WS, CHAINW s BH BP WS.

Lemma CHAIN_mono : forall s BH BP BH' BP', BH <= BH' -> BP <= BP' -> CHAIN s BH BP -> CHAIN s BH' BP'.
Proof.
  intros s BH BP BH' BP' L1 L2 (WS & H1 & H2). exists WS. split.
  - intros h Hh. destruct (H1 h Hh) as [E|[B W]]; [left; exact E | right; split; [lia | exact W]].
  - intros q Hq. destruct (H2 q Hq) as [R [E|[B W]]]; (split; [exact R|]); [left; exact E | right; split; [lia | exact W]].
Qed.

Lemma CHAIN_same : forall s s' BH BP,
  ds_head s' = ds_head s -> ds_prev s' = ds_prev s -> ds_hash_size s' = ds_hash_size s ->
  ds_w_size s' = ds_w_size s -> ds_w_mask s' = ds_w_mask s ->
  CHAIN s BH BP -> CHAIN s' BH BP.
Proof.
  intros s s' BH BP E1 E2 E3 E4 E5 (WS & H1 & H2). exists WS. unfold CHAINW. rewrite E1, E2, E3, E4, E5. exact (conj H1 H2).
Qed.

Lemma CHAIN_heads0 : forall s BH BP,
  (forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head s) h = 0) -> CHAIN s BH BP.
Proof.
  intros s BH BP H0. exists (fun _ => False). split.
  - intros h Hh. left. exact (H0 h Hh).
  - intros q Hq. destruct Hq.
Qed.

Lemma CHAIN_clear_hash : forall s BH BP,
  arr_len (ds_head s) = ds_hash_size s -> 1 <= ds_hash_size s -> CHAIN (clear_hash s) BH BP.
Proof.
  intros s BH BP Hl Hs. apply CHAIN_heads0. unfold clear_hash. cbn [ds_head ds_hash_size set_head].
  change (ds_hash_size (set_head (set_head s (arr_set (ds_head s) (ds_hash_size s - 1) NIL))
            (arr_fill (ds_head (set_head s (arr_set (ds_head s) (ds_hash_size s - 1) NIL))) 0 (ds_hash_size s - 1) 0)))
    with (ds_hash_size s).
  change (ds_head (set_head (set_head s (arr_set (ds_head s) (ds_hash_size s - 1) NIL))
            (arr_fill (ds_head (set_head s (arr_set (ds_head s) (ds_hash_size s - 1) NIL))) 0 (ds_hash_size s - 1) 0)))
    with (arr_fill (arr_set (ds_head s) (ds_hash_size s - 1) NIL) 0 (ds_hash_size s - 1) 0).
  intros h Hh. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Hl.
  destruct (Z.eq_dec h (ds_hash_size s - 1)) as [->|Hne].
  - replace ((0 <=? ds_hash_size s - 1) && (ds_hash_size s - 1 <? 0 + Z.max 0 (ds_hash_size s - 1)) && _) with false
      by (symmetry; apply Bool.andb_false_iff; left; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
    unfold NIL. apply arr_get_set_same. rewrite Hl. lia.
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with true; [reflexivity|].
    symmetry. rewrite !Bool.andb_true_iff. repeat split; first [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.


Section Pow2.
  Lemma land_wmask : forall k x, 0 <= k -> Z.land x (2 ^ k - 1) = x mod 2 ^ k.
  Proof. intros k x Hk. rewrite <- Z.land_ones by exact Hk. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.

  Lemma land_wmask_range : forall k x, 0 <= k -> 0 <= Z.land x (2 ^ k - 1) < 2 ^ k.
  Proof. intros k x Hk. rewrite land_wmask by exact Hk. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

  Lemma land_wmask_sub : forall k x, 0 <= k -> Z.land (x - 2 ^ k) (2 ^ k - 1) = Z.land x (2 ^ k - 1).
  Proof.
    intros k x Hk. rewrite !land_wmask by exact Hk.
    replace (x - 2 ^ k) with (x + (-1) * 2 ^ k) by lia. apply Z.mod_add. apply Z.pow_nonzero; lia.
  Qed.
End Pow2.

Lemma insert_string_eq : forall s str,
  insert_string s str =
  (let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
   (set_head (set_prev (set_ins_h s h) (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)))
             (arr_set (ds_head s) h (wrap16 str)),
    arr_get (ds_head s) h)).
Proof. intros; reflexivity. Qed.

Lemma CHAIN_insert_string : forall s str BH BP k,
  CHAIN s BH BP ->
  ds_w_size s = 2 ^ k -> 0 <= k -> ds_w_mask s = ds_w_size s - 1 -> arr_len (ds_prev s) = ds_w_size s ->
  arr_len (ds_head s) = ds_hash_size s -> 0 <= ds_hash_mask s -> ds_hash_mask s = ds_hash_size s - 1 ->
  0 <= str < 2 ^ 16 ->
  CHAIN (fst (insert_string s str)) (Z.max BH str) (Z.max BP BH)
  /\ (snd (insert_string s str) = 0 \/ 1 <= snd (insert_string s str) <= BH).
Proof.
  intros s str BH BP k (WS & H1 & H2) Ews Hk Ewm Lp Lh Hm0 Ehm Hstr.
  rewrite insert_string_eq. cbv zeta. cbn [fst snd].
  set (h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1)))).
  pose proof (update_hash_range s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) Hm0) as Hh. fold h in Hh.
  rewrite Ehm in Hh.
  assert (Ew16 : wrap16 str = str) by (rewrite wrap16_mod; apply Z.mod_small; lia).
  pose proof (land_wmask_range k str Hk) as Hslot. rewrite <- Ews, <- Ewm in Hslot.
  split.
  - exists (fun q => WS q \/ q = Z.land str (ds_w_mask s)). unfold CHAINW.
    cbn [ds_head ds_prev ds_hash_size ds_w_size ds_w_mask set_head set_prev set_ins_h].
    change (ds_hash_size (set_head _ _)) with (ds_hash_size s).
    change (ds_w_mask (set_head _ _)) with (ds_w_mask s).
    change (ds_w_size (set_head _ _)) with (ds_w_size s).
    change (ds_head (set_head _ ?a)) with a.
    change (ds_prev (set_head (set_prev _ ?a) _)) with a.
    split.
    + intros h' Hh'. rewrite arr_get_set. unfold arr_inb. rewrite Lh.
      destruct (Z.eqb_spec h h') as [<-|Hne]; cbn [andb].
      * replace ((0 <=? h) && (h <? ds_hash_size s)) with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        rewrite Ew16. destruct (Z.eq_dec str 0) as [->|Hnz]; [left; reflexivity | right]. split; [lia|]. right. reflexivity.
      * destruct (H1 h' Hh') as [E|[B W]]; [left; exact E | right]. split; [lia|]. left. exact W.
    + intros q [Hq | ->].
      * destruct (H2 q Hq) as [Rq Pq]. split; [exact Rq|].
        rewrite arr_get_set. unfold arr_inb. rewrite Lp.
        destruct (Z.eqb_spec (Z.land str (ds_w_mask s)) q) as [<-|Hne]; cbn [andb].
        -- replace ((0 <=? Z.land str (ds_w_mask s)) && (Z.land str (ds_w_mask s) <? ds_w_size s)) with true
             by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
           destruct (H1 h ltac:(lia)) as [E|[B W]]; [left; exact E | right]. split; [lia|]. left. exact W.
        -- destruct Pq as [E|[B W]]; [left; exact E | right]. split; [lia|]. left. exact W.
      * split; [lia|].
        rewrite arr_get_set_same by (rewrite Lp; lia).
        destruct (H1 h ltac:(lia)) as [E|[B W]]; [left; exact E | right]. split; [lia|]. left. exact W.
  - destruct (H1 h ltac:(lia)) as [E|[B W]]; [left; exact E | right; exact B].
Qed.


Lemma slide_hash_eq : forall s,
  slide_hash s = set_prev (set_head s (slide_hash_loop (Z.to_nat (ds_hash_size s)) (ds_head s) (ds_hash_size s) (ds_w_size s)))
                          (slide_hash_loop (Z.to_nat (ds_w_size s)) (ds_prev s) (ds_w_size s) (ds_w_size s)).
Proof. intros s. unfold slide_hash. destruct s; reflexivity. Qed.

Lemma CHAIN_slide_hash : forall s BH BP k,
  CHAIN s BH BP ->
  ds_w_size s = 2 ^ k -> 0 <= k -> ds_w_mask s = ds_w_size s - 1 -> arr_len (ds_prev s) = ds_w_size s ->
  arr_len (ds_head s) = ds_hash_size s -> 0 <= ds_hash_size s ->
  (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s) i < 65536) ->
  (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536) ->
  CHAIN (slide_hash s) (BH - ds_w_size s) (BP - ds_w_size s).
Proof.
  intros s BH BP k (WS & H1 & H2) Ews Hk Ewm Lp Lh Hhs Hhb Hpb.
  assert (Hws : 0 < ds_w_size s) by (rewrite Ews; apply Z.pow_pos_nonneg; lia).
  exists WS. rewrite slide_hash_eq. unfold CHAINW.
  change (ds_hash_size (set_prev (set_head s ?a) ?b)) with (ds_hash_size s).
  change (ds_w_size (set_prev (set_head s ?a) ?b)) with (ds_w_size s).
  change (ds_w_mask (set_prev (set_head s ?a) ?b)) with (ds_w_mask s).
  change (ds_head (set_prev (set_head s ?a) ?b)) with a.
  change (ds_prev (set_prev (set_head s ?a) ?b)) with b.
  assert (SHM : forall m, 0 <= m < 65536 ->
            shm (ds_w_size s) m = (if ds_w_size s <=? m then m - ds_w_size s else 0)).
  { intros m Hm. unfold shm, NIL. rewrite wrap16_mod. apply Z.mod_small. destruct (Z.leb_spec (ds_w_size s) m); lia. }
  split.
  - intros h Hh. rewrite (slide_hash_loop_get _ _ _ _ (ds_hash_size s)) by (first [rewrite Z2Nat.id; lia | rewrite Lh; lia]).
    replace ((0 <=? h) && (h <? ds_hash_size s)) with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite SHM by (apply Hhb; exact Hh).
    destruct (H1 h Hh) as [E|[B W]]; [rewrite E; left; destruct (Z.leb_spec (ds_w_size s) 0); lia|].
    destruct (Z.leb_spec (ds_w_size s) (arr_get (ds_head s) h)) as [L|L]; [|left; reflexivity].
    destruct (Z.eq_dec (arr_get (ds_head s) h) (ds_w_size s)) as [E|Hne]; [left; lia | right].
    split; [lia|]. rewrite Ewm, Ews, land_wmask_sub by exact Hk. rewrite <- Ews, <- Ewm. exact W.
  - intros q Hq. destruct (H2 q Hq) as [Rq Pq]. split; [exact Rq|].
    rewrite (slide_hash_loop_get _ _ _ _ (ds_w_size s)) by (first [rewrite Z2Nat.id; lia | rewrite Lp; lia]).
    replace ((0 <=? q) && (q <? ds_w_size s)) with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite SHM by (apply Hpb; exact Rq).
    destruct Pq as [E|[B W]]; [rewrite E; left; destruct (Z.leb_spec (ds_w_size s) 0); lia|].
    destruct (Z.leb_spec (ds_w_size s) (arr_get (ds_prev s) q)) as [L|L]; [|left; reflexivity].
    destruct (Z.eq_dec (arr_get (ds_prev s) q) (ds_w_size s)) as [E|Hne]; [left; lia | right].
    split; [lia|]. rewrite Ewm, Ews, land_wmask_sub by exact Hk. rewrite <- Ews, <- Ewm. exact W.
Qed.


Lemma lmb_cont : forall s cur ch bl nice limit se1 se s' b' se1' se' cur' ch',
  longest_match_body s cur ch bl nice limit se1 se = (s', b', se1', se', cur', ch', true) ->
  cur' = arr_get (ds_prev s) (Z.land cur (ds_w_mask s)) /\ limit < cur' /\ (s' = s \/ s' = set_match_start s cur).
Proof.
  intros s cur ch bl nice limit se1 se s' b' se1' se' cur' ch' E.
  unfold longest_match_body in E. cbv zeta in E.
  destruct (_ || _ || _ || _).
  - destruct (Z.ltb_spec limit (arr_get (ds_prev s) (Z.land cur (ds_w_mask s)))) as [L|L].
    + destruct (negb _); injection E as <- <- <- <- <- <- ; [split; [reflexivity | split; [exact L | left; reflexivity]]|].
      all: try discriminate.
    + injection E as <- <- <- <- <- <- . all: discriminate.
  - destruct (bl <? _).
    + destruct (nice <=? _).
      * injection E as <- <- <- <- <- <- . all: discriminate.
      * change (ds_prev (set_match_start s cur)) with (ds_prev s) in E. change (ds_w_mask (set_match_start s cur)) with (ds_w_mask s) in E.
        destruct (Z.ltb_spec limit (arr_get (ds_prev s) (Z.land cur (ds_w_mask s)))) as [L|L].
        -- destruct (negb _); injection E as <- <- <- <- <- <- ; [split; [reflexivity | split; [exact L | right; reflexivity]]|].
           all: try discriminate.
        -- injection E as <- <- <- <- <- <- . all: discriminate.
    + destruct (Z.ltb_spec limit (arr_get (ds_prev s) (Z.land cur (ds_w_mask s)))) as [L|L].
      * destruct (negb _); injection E as <- <- <- <- <- <- ; [split; [reflexivity | split; [exact L | left; reflexivity]]|].
        all: try discriminate.
      * injection E as <- <- <- <- <- <- . all: discriminate.
Qed.

Lemma lm_curs_bound : forall f s cur ch bl nice limit se1 se BP WS,
  (forall q, WS q -> 0 <= q < ds_w_size s /\ (arr_get (ds_prev s) q = 0 \/ (1 <= arr_get (ds_prev s) q <= BP /\ WS (Z.land (arr_get (ds_prev s) q) (ds_w_mask s))))) ->
  0 <= limit ->
  1 <= cur -> WS (Z.land cur (ds_w_mask s)) ->
  Forall (fun c => 1 <= c <= Z.max cur BP) (lm_curs f s cur ch bl nice limit se1 se).
Proof.
  induction f as [|f IH]; intros s cur ch bl nice limit se1 se BP WS H2 Hlim Hc1 Hcw.
  - cbn [lm_curs]. constructor; [lia | constructor].
  - cbn [lm_curs].
    constructor; [lia|].
    destruct (longest_match_body s cur ch bl nice limit se1 se) as [[[[[[s' b'] se1'] se'] cur'] ch'] cont] eqn:E.
    destruct cont; [|constructor].
    destruct (lmb_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ E) as (Ecur' & Hlt & Es').
    destruct (H2 _ Hcw) as [_ [Z0|[B W]]]; [rewrite <- Ecur' in Z0; lia|]. rewrite <- Ecur' in B, W.
    assert (Es : ds_prev s' = ds_prev s /\ ds_w_mask s' = ds_w_mask s /\ ds_w_size s' = ds_w_size s)
      by (destruct Es' as [-> | ->]; repeat split; reflexivity).
    destruct Es as (Ep' & Em' & Ew').
    eapply Forall_impl; [| apply (IH s' cur' ch' b' nice limit se1' se' BP WS); [rewrite Ep', Em', Ew'; exact H2 | exact Hlim | lia | rewrite Em'; exact W]].
    intros c Hc. cbv beta in Hc. lia.
Qed.

Lemma lm_visited_bound : forall s1 str k,
  CHAIN s1 (str - 1) (str - 1) ->
  ds_w_size s1 = 2 ^ k -> 0 <= k -> ds_w_mask s1 = ds_w_size s1 - 1 -> arr_len (ds_prev s1) = ds_w_size s1 ->
  arr_len (ds_head s1) = ds_hash_size s1 -> 0 <= ds_hash_mask s1 -> ds_hash_mask s1 = ds_hash_size s1 - 1 ->
  0 <= str < 2 ^ 16 -> MIN_LOOKAHEAD <= ds_w_size s1 ->
  let s2 := fst (insert_string s1 str) in
  let cur := snd (insert_string s1 str) in
  cur <> 0 -> ds_strstart s2 = str ->
  Forall (fun c => 0 <= c < ds_strstart s2) (lm_visited s2 cur).
Proof.
  intros s1 str k HC Ews Hk Ewm Lp Lh Hm0 Ehm Hstr Hmla s2 cur Hnz Estr.
  destruct (CHAIN_insert_string s1 str (str - 1) (str - 1) k HC Ews Hk Ewm Lp Lh Hm0 Ehm Hstr) as [(WS & H1 & H2) Hcur].
  fold s2 in H1, H2. fold cur in Hcur.
  destruct Hcur as [Z0|B]; [exfalso; exact (Hnz Z0)|].
  unfold lm_visited. cbv zeta. rewrite Estr.
  assert (Hcw : WS (Z.land cur (ds_w_mask s2))).
  {
    assert (Hslot : WS (Z.land str (ds_w_mask s1))).
    {
      subst s2 cur. rewrite insert_string_eq in H1. cbv zeta in H1. cbn [fst snd] in H1.
      set (h := update_hash s1 (ds_ins_h s1) (arr_get (ds_window s1) (str + (MIN_MATCH - 1)))) in *.
      pose proof (update_hash_range s1 (ds_ins_h s1) (arr_get (ds_window s1) (str + (MIN_MATCH - 1))) Hm0) as Hh. fold h in Hh. rewrite Ehm in Hh.
      specialize (H1 h). 
      change (ds_hash_size (set_head ?x ?a)) with (ds_hash_size s1) in H1.
      change (ds_head (set_head ?x ?a)) with a in H1.
      change (ds_w_mask (set_head ?x ?a)) with (ds_w_mask s1) in H1.
      specialize (H1 ltac:(lia)). rewrite arr_get_set_same in H1 by (rewrite Lh; lia).
      assert (Ew16 : wrap16 str = str) by (rewrite wrap16_mod; apply Z.mod_small; lia). rewrite Ew16 in H1.
      destruct H1 as [S0|[_ W]]; [|exact W].
      exfalso. lia. }
    pose proof (H2 _ Hslot) as [_ P].
    subst s2 cur. rewrite insert_string_eq in P |- *. cbv zeta in P. cbn [fst snd] in P |- *.
    change (ds_prev (set_head (set_prev ?x ?b) ?a)) with b in P.
    change (ds_w_mask (set_head (set_prev (set_ins_h s1 ?hh) ?b) ?a)) with (ds_w_mask s1) in P |- *.
    rewrite arr_get_set_same in P by (rewrite Lp; pose proof (land_wmask_range k str Hk); rewrite <- Ews, <- Ewm in *; lia).
    destruct P as [Z0|[_ W]]; [exfalso; rewrite insert_string_eq in B; cbv zeta in B; cbn [snd] in B; lia | exact W]. }
  match goal with |- Forall _ (lm_curs ?f _ _ ?ch ?bl ?nice ?limit ?se1 ?se) =>
    pose proof (lm_curs_bound f s2 cur ch bl nice limit se1 se (Z.max (str - 1) (str - 1)) WS H2) as HB end.
  eapply Forall_impl; [| apply HB; [| lia | exact Hcw]].
  - intros c Hc. cbv beta in Hc. lia.
  - assert (Ews2 : ds_w_size s2 = ds_w_size s1) by (subst s2; rewrite insert_string_eq; reflexivity).
    rewrite Ews2. unfold NIL, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. destruct (Z.ltb_spec (ds_w_size s1 - (258 + 3 + 1)) str); lia.
Qed.
