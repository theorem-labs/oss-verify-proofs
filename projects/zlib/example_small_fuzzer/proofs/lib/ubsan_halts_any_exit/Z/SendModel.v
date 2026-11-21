(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.

Module ScanModel.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sbf_twice : forall s a b, set_bl_tree_fc (set_bl_tree_fc s a) b = set_bl_tree_fc s b.
Proof. intros. reflexivity. Qed.
Lemma sbf_self : forall s, set_bl_tree_fc s (ds_bl_tree_fc s) = s.
Proof. intros s. destruct s; reflexivity. Qed.
Lemma sbf_get : forall s b, ds_bl_tree_fc (set_bl_tree_fc s b) = b.
Proof. intros. reflexivity. Qed.
Lemma sbf_tree_dl : forall s b t, tree_dl (set_bl_tree_fc s b) t = tree_dl s t.
Proof. intros s b [| |]; reflexivity. Qed.
Lemma sbf_Len : forall s b t n, Len (set_bl_tree_fc s b) t n = Len s t n.
Proof. intros. unfold Len. rewrite sbf_tree_dl. reflexivity. Qed.
Lemma sbf_FreqB : forall s b n, Freq (set_bl_tree_fc s b) TB n = arr_get b n.
Proof. intros. reflexivity. Qed.
Lemma sbf_set_FreqB : forall s b n v,
  set_Freq (set_bl_tree_fc s b) TB n v = set_bl_tree_fc s (arr_set b n (wrap16 v)).
Proof. intros. reflexivity. Qed.
Lemma sbf_tree_fc : forall s b t, t <> TB -> tree_fc (set_bl_tree_fc s b) t = tree_fc s t.
Proof. intros s b [| |] H; [reflexivity | reflexivity | congruence]. Qed.

Lemma Len_set_Len : forall s t i v n, 0 <= i < arr_len (tree_dl s t) ->
  Len (set_Len s t i v) t n = if i =? n then wrap16 v else Len s t n.
Proof.
  intros s t i v n Hi. unfold Len, set_Len, set_Dad.
  destruct t; cbn [tree_dl set_tree_dl]; dsred; rewrite arr_get_set; unfold arr_inb;
    cbn [tree_dl] in Hi;
    destruct (Z.eqb_spec i n), (Z.leb_spec 0 i); cbn [andb]; try lia;
    [destruct (Z.ltb_spec i (arr_len (ds_dyn_ltree_dl s))) | destruct (Z.ltb_spec i (arr_len (ds_dyn_dtree_dl s)))
    | destruct (Z.ltb_spec i (arr_len (ds_bl_tree_dl s)))]; cbn; try lia; reflexivity.
Qed.

Lemma tree_dl_len_set_Len : forall s t i v t', arr_len (tree_dl (set_Len s t i v) t') = arr_len (tree_dl s t').
Proof. intros s [| |] i v [| |]; cbn [tree_dl set_Len set_Dad set_tree_dl]; dsred; rewrite ?arr_len_set; reflexivity. Qed.
Lemma tree_fc_set_Len : forall s t i v t', tree_fc (set_Len s t i v) t' = tree_fc s t'.
Proof. intros s [| |] i v [| |]; reflexivity. Qed.

Definition st_upd (mn : Z) (b : arr) (curlen prevlen count : Z) : arr :=
  if count <? mn then arr_set b curlen (wrap16 (arr_get b curlen + count))
  else if negb (curlen =? 0) then
    let b := if negb (curlen =? prevlen) then arr_set b curlen (wrap16 (arr_get b curlen + 1)) else b in
    arr_set b REP_3_6 (wrap16 (arr_get b REP_3_6 + 1))
  else if count <=? 10 then arr_set b REPZ_3_10 (wrap16 (arr_get b REPZ_3_10 + 1))
  else arr_set b REPZ_11_138 (wrap16 (arr_get b REPZ_11_138 + 1)).

Lemma st_upd_len : forall mn b c p k, arr_len (st_upd mn b c p k) = arr_len b.
Proof.
  intros. unfold st_upd.
  destruct (k <? mn); [apply arr_len_set|].
  destruct (negb (c =? 0)); [destruct (negb (c =? p)); rewrite ?arr_len_set; reflexivity|].
  destruct (k <=? 10); apply arr_len_set.
Qed.

Lemma st_upd_range : forall mn b c p k,
  (forall i, 0 <= i < arr_len b -> 0 <= arr_get b i < 65536) ->
  forall i, 0 <= i < arr_len b -> 0 <= arr_get (st_upd mn b c p k) i < 65536.
Proof.
  intros mn b c p k Hb i Hi.
  assert (W : forall x, 0 <= wrap16 x < 65536).
  { intros x. rewrite wrap16_mod. change (2 ^ 16) with 65536. apply Z.mod_pos_bound. lia. }
  assert (G : forall a j v q, (forall r, 0 <= r < arr_len a -> 0 <= arr_get a r < 65536) ->
             0 <= q < arr_len a -> 0 <= arr_get (arr_set a j (wrap16 v)) q < 65536).
  { intros a j v q Hr Hq. rewrite arr_get_set. destruct (_ && _); [apply W | apply Hr; exact Hq]. }
  unfold st_upd.
  destruct (k <? mn); [apply G; [exact Hb | exact Hi]|].
  destruct (negb (c =? 0)).
  - destruct (negb (c =? p)).
    + apply G; [| rewrite arr_len_set; exact Hi].
      intros r Hr. rewrite arr_len_set in Hr. apply G; [exact Hb | exact Hr].
    + apply G; [exact Hb | exact Hi].
  - destruct (k <=? 10); apply G; (exact Hb || exact Hi).
Qed.

Lemma scan_loop_S : forall f s0 b t mc n prevlen nextlen count mx mn,
  scan_tree_loop (S f) (set_bl_tree_fc s0 b) t mc n prevlen nextlen count mx mn =
    if n <=? mc then
      let curlen := nextlen in
      let nextlen' := Len s0 t (n + 1) in
      let count' := count + 1 in
      if (count' <? mx) && (curlen =? nextlen') then
        scan_tree_loop f (set_bl_tree_fc s0 b) t mc (n + 1) prevlen nextlen' count' mx mn
      else
        let '(mx', mn') := tree_counts curlen nextlen' in
        scan_tree_loop f (set_bl_tree_fc s0 (st_upd mn b curlen prevlen count')) t mc (n + 1)
                       curlen nextlen' 0 mx' mn'
    else set_bl_tree_fc s0 b.
Proof.
  intros. cbn [scan_tree_loop]. rewrite sbf_Len.
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((count + 1 <? mx) && (nextlen =? Len s0 t (n + 1))); [reflexivity|].
  unfold st_upd. rewrite !sbf_FreqB.
  destruct (count + 1 <? mn); [reflexivity|].
  destruct (negb (nextlen =? 0)).
  - destruct (negb (nextlen =? prevlen)); reflexivity.
  - destruct (count + 1 <=? 10); reflexivity.
Qed.

Lemma scan_loop_0 : forall s t mc n p q c mx mn, scan_tree_loop 0 s t mc n p q c mx mn = s.
Proof. reflexivity. Qed.

Lemma scan_loop_out : forall f s t mc n p q c mx mn, mc < n -> scan_tree_loop f s t mc n p q c mx mn = s.
Proof.
  intros [|f] s t mc n p q c mx mn H; [reflexivity|]. cbn [scan_tree_loop].
  destruct (Z.leb_spec n mc); [lia | reflexivity].
Qed.

Lemma scan_loop_shape : forall f s0 b t mc n p q c mx mn,
  exists b', scan_tree_loop f (set_bl_tree_fc s0 b) t mc n p q c mx mn = set_bl_tree_fc s0 b'
             /\ arr_len b' = arr_len b
             /\ ((forall i, 0 <= i < arr_len b -> 0 <= arr_get b i < 65536) ->
                 forall i, 0 <= i < arr_len b' -> 0 <= arr_get b' i < 65536).
Proof.
  induction f as [|f IH]; intros.
  - exists b. rewrite scan_loop_0. auto.
  - rewrite scan_loop_S. destruct (n <=? mc); [| exists b; auto]. cbv zeta.
    destruct ((c + 1 <? mx) && (q =? Len s0 t (n + 1))); [apply IH|].
    destruct (tree_counts q (Len s0 t (n + 1))) as [mx' mn'].
    destruct (IH s0 (st_upd mn b q p (c + 1)) t mc (n + 1) q (Len s0 t (n + 1)) 0 mx' mn') as (b' & E & L & R).
    exists b'. split; [exact E|]. rewrite st_upd_len in L, R. split; [exact L|].
    intros Hb. apply R. apply st_upd_range. exact Hb.
Qed.

Lemma tree_counts_range : forall a b mx mn, tree_counts a b = (mx, mn) -> (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4).
Proof.
  intros a b mx mn H. unfold tree_counts in H.
  destruct (b =? 0); [|destruct (a =? b)]; injection H as <- <-; lia.
Qed.
End ScanModel.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel.

Module RefDeflSafeL1.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
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
End RefDeflSafeL1.

Module RefLmatch_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable sp : Z.
Variable ds : deflate_state.
Local Notation w := (ds_window ds).
Local Notation pv := (ds_prev ds).
Local Notation WL := (arr_len (ds_window ds)).
Local Notation PL := (arr_len (ds_prev ds)).
Local Notation strstart := (ds_strstart ds).
Local Notation strend := (ds_strstart ds + 258).
Hypothesis Hwb : forall i, 0 <= i < WL -> 0 <= arr_get w i < 256.
Hypothesis Hpb : forall i, 0 <= i < PL -> 0 <= arr_get pv i < 65536.
Hypothesis Hsp : 32 <= sp /\ sp <= 2 ^ 63.
Hypothesis Hstr : 0 <= strstart /\ strstart + 258 < WL /\ WL <= 2 ^ 31.
Hypothesis Hwm : 0 <= ds_w_mask ds < PL /\ PL <= 2 ^ 31.
Hypothesis Hpl : 1 <= ds_prev_length ds <= 258.
Hypothesis Hnice : 0 <= ds_nice_match ds <= 258.
Hypothesis Hlook : 0 <= ds_lookahead ds < 2 ^ 31.
Hypothesis Hgood : 0 <= ds_good_match ds < 2 ^ 31.
Hypothesis Hchain : 0 <= ds_max_chain_length ds < 2 ^ 31.
Hypothesis Hwsz : 262 <= ds_w_size ds < 2 ^ 31.

Definition LF : franges := [(sp - 32, 32); (S + 176, 4)].



Let F1 : nat -> Z -> Z := fun f => match f with 0%nat => wb w | _ => pb pv end.
Let HF0 : forall x, 0 <= F1 0%nat x < 256 := fun x => wb_range w x.
Let HF1 : forall x, 0 <= F1 1%nat x < 65536 := fun x => pb_range pv x.

Let wb_eqI : forall i j, arr_get w i = arr_get w j -> wb w i = wb w j := wb_eqI w.
Let wb_neI : forall i j, 0 <= i < WL -> 0 <= j < WL -> arr_get w i <> arr_get w j -> wb w i <> wb w j
  := wb_neI w Hwb.
Let wb_get : forall i, 0 <= i < WL -> wb w i = arr_get w i := wb_get w Hwb.
Let pb_get : forall i, 0 <= i < PL -> pb pv i = arr_get pv i := pb_get pv Hpb.

Local Ltac norm_idx :=
  repeat match goal with
  | |- context [?x + Zpos ?a + Zpos ?b] =>
      let c := eval vm_compute in (Zpos a + Zpos b) in
      replace (x + Zpos a + Zpos b) with (x + c) by lia
  end.

End Walk.

End RefLmatch_run.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition upd4 (s : deflate_state) (pb : arr) (pd bb bv : Z) : deflate_state :=
  set_bi_valid (set_bi_buf (set_pending (set_pending_buf s pb) pd) bb) bv.

Lemma send_bits_shape : forall s v l,
  send_bits s v l = upd4 s (ds_pending_buf (send_bits s v l)) (ds_pending (send_bits s v l))
                           (ds_bi_buf (send_bits s v l)) (ds_bi_valid (send_bits s v l)).
Proof.
  intros s v l. unfold send_bits, put_short, put_byte, upd4.
  destruct (Buf_size - l <? ds_bi_valid s); reflexivity.
Qed.

Lemma upd4_tree_fc : forall s pb pd bb bv t, tree_fc (upd4 s pb pd bb bv) t = tree_fc s t.
Proof. intros s pb pd bb bv [| |]; reflexivity. Qed.
Lemma upd4_tree_dl : forall s pb pd bb bv t, tree_dl (upd4 s pb pd bb bv) t = tree_dl s t.
Proof. intros s pb pd bb bv [| |]; reflexivity. Qed.

Lemma sb_tree_fc : forall s v l t, tree_fc (send_bits s v l) t = tree_fc s t.
Proof. intros. rewrite send_bits_shape. apply upd4_tree_fc. Qed.
Lemma sb_tree_dl : forall s v l t, tree_dl (send_bits s v l) t = tree_dl s t.
Proof. intros. rewrite send_bits_shape. apply upd4_tree_dl. Qed.
Lemma sb_Len : forall s v l t n, Len (send_bits s v l) t n = Len s t n.
Proof. intros. unfold Len. rewrite sb_tree_dl. reflexivity. Qed.
Lemma sb_Code : forall s v l t n, Code (send_bits s v l) t n = Code s t n.
Proof. intros. unfold Code. rewrite sb_tree_fc. reflexivity. Qed.
Lemma sb_pbl : forall s v l, arr_len (ds_pending_buf (send_bits s v l)) = arr_len (ds_pending_buf s).
Proof.
  intros s v l. unfold send_bits, put_short, put_byte.
  destruct (Buf_size - l <? ds_bi_valid s); dsred; rewrite ?arr_len_set; reflexivity.
Qed.
Lemma sb_lens : forall s v l, tree_lens s -> tree_lens (send_bits s v l).
Proof. intros s v l H. rewrite send_bits_shape. unfold upd4, tree_lens in *. dsred. exact H. Qed.

Lemma send_bits_wrap : forall s v v' l, wrap16 v' = wrap16 v -> send_bits s v' l = send_bits s v l.
Proof. intros s v v' l E. unfold send_bits. rewrite !E. reflexivity. Qed.

Lemma wrap16_szwrap32 : forall x, wrap16 (SymEx2Expr.szwrap 32 x) = wrap16 x.
Proof.
  intros x. rewrite !wrap16_mod'. rewrite <- (mod_pow2_mod_pow2 (SymEx2Expr.szwrap 32 x) 32 16) by lia.
  rewrite SymEx2Expr.szwrap_eqm by lia. apply mod_pow2_mod_pow2. lia.
Qed.


Definition BINV (PBL : Z) (s : deflate_state) : Prop :=
  0 <= ds_bi_valid s <= 16 /\ 0 <= ds_bi_buf s < 2 ^ 16 /\ 0 <= ds_pending s <= PBL.

Definition sb_room (PBL : Z) (s : deflate_state) (l : Z) : Prop :=
  Buf_size - l < ds_bi_valid s -> ds_pending s + 2 <= PBL.

Lemma wrap16_range' : forall z, 0 <= wrap16 z < 2 ^ 16.
Proof. intros z. rewrite wrap16_mod'. apply Z.mod_pos_bound. lia. Qed.

Lemma send_bits_BINV : forall PBL s v l,
  BINV PBL s -> 0 <= l <= 16 -> sb_room PBL s l -> BINV PBL (send_bits s v l).
Proof.
  intros PBL s v l (Hbv & Hbb & Hpd) Hl Hroom. unfold sb_room, Buf_size in *.
  unfold send_bits, Buf_size, put_short, put_byte, BINV.
  destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)) as [C|C]; dsred.
  - specialize (Hroom C). split; [lia|]. split; [|lia].
    pose proof (wrap16_range' v) as W. rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Z.pow_pos_nonneg 2 (16 - ds_bi_valid s) ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
  - split; [lia|]. split; [apply wrap16_range'|]. lia.
Qed.


Fixpoint sbs_run (s : deflate_state) (cs : list (Z * Z)) : deflate_state :=
  match cs with
  | [] => s
  | (v, l) :: r => sbs_run (send_bits s v l) r
  end.

Fixpoint sbs_ok (PBL : Z) (s : deflate_state) (cs : list (Z * Z)) : Prop :=
  match cs with
  | [] => True
  | (v, l) :: r => 0 <= l <= 16 /\ sb_room PBL s l /\ sbs_ok PBL (send_bits s v l) r
  end.

Lemma sbs_run_app : forall s a b, sbs_run s (a ++ b) = sbs_run (sbs_run s a) b.
Proof. intros s a. revert s. induction a as [|[v l] a IH]; intros; [reflexivity|]. cbn. apply IH. Qed.

Lemma sbs_ok_app : forall PBL s a b, sbs_ok PBL s (a ++ b) <-> sbs_ok PBL s a /\ sbs_ok PBL (sbs_run s a) b.
Proof.
  intros PBL s a. revert s. induction a as [|[v l] a IH]; intros; cbn; [tauto|].
  rewrite IH. tauto.
Qed.

Lemma sbs_BINV : forall PBL cs s, BINV PBL s -> sbs_ok PBL s cs -> BINV PBL (sbs_run s cs).
Proof.
  induction cs as [|[v l] cs IH]; intros s HB Hok; [exact HB|].
  cbn in *. destruct Hok as (Hl & Hr & Hok). apply IH; [apply send_bits_BINV; assumption | exact Hok].
Qed.

Lemma sbs_tree_fc : forall cs s t, tree_fc (sbs_run s cs) t = tree_fc s t.
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply sb_tree_fc. Qed.
Lemma sbs_tree_dl : forall cs s t, tree_dl (sbs_run s cs) t = tree_dl s t.
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply sb_tree_dl. Qed.
Lemma sbs_Len : forall cs s t n, Len (sbs_run s cs) t n = Len s t n.
Proof. intros. unfold Len. rewrite sbs_tree_dl. reflexivity. Qed.
Lemma sbs_Code : forall cs s t n, Code (sbs_run s cs) t n = Code s t n.
Proof. intros. unfold Code. rewrite sbs_tree_fc. reflexivity. Qed.
Lemma sbs_pbl : forall cs s, arr_len (ds_pending_buf (sbs_run s cs)) = arr_len (ds_pending_buf s).
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply sb_pbl. Qed.
Lemma sbs_lens : forall cs s, tree_lens s -> tree_lens (sbs_run s cs).
Proof. induction cs as [|[v l] cs IH]; intros s H; [exact H|]. cbn. apply IH. apply sb_lens. exact H. Qed.


Definition blc (s : deflate_state) (c : Z) : Z * Z := (Code s TB c, Len s TB c).

Definition st_calls (s : deflate_state) (mn curlen prevlen count : Z) : list (Z * Z) :=
  if count <? mn then repeat (blc s curlen) (Z.to_nat count)
  else if negb (curlen =? 0) then
    (if negb (curlen =? prevlen) then [blc s curlen] else [])
      ++ [blc s REP_3_6; ((if negb (curlen =? prevlen) then count - 1 else count) - 3, 2)]
  else if count <=? 10 then [blc s REPZ_3_10; (count - 3, 3)]
  else [blc s REPZ_11_138; (count - 11, 7)].

Lemma send_tree_rep_sbs : forall k s c count,
  (1 <= k)%nat -> count = Z.of_nat k ->
  send_tree_rep k s c count = sbs_run s (repeat (blc s c) k).
Proof.
  induction k as [|k IH]; intros s c count Hk Hc; [lia|].
  cbn [send_tree_rep repeat sbs_run]. unfold send_dcode, blc.
  destruct k as [|k'].
  - cbn [repeat sbs_run]. replace (count - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (count - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    rewrite (IH _ c (count - 1)) by lia.
    unfold blc. rewrite sb_Code, sb_Len. reflexivity.
Qed.

Lemma send_loop_S : forall f s t mc n prevlen nextlen count mx mn,
  1 <= mn ->
  send_tree_loop (S f) s t mc n prevlen nextlen count mx mn =
    if n <=? mc then
      let curlen := nextlen in
      let nextlen' := Len s t (n + 1) in
      let count' := count + 1 in
      if (count' <? mx) && (curlen =? nextlen') then
        send_tree_loop f s t mc (n + 1) prevlen nextlen' count' mx mn
      else
        let '(mx', mn') := tree_counts curlen nextlen' in
        send_tree_loop f (sbs_run s (st_calls s mn curlen prevlen count')) t mc (n + 1)
                       curlen nextlen' 0 mx' mn'
    else s.
Proof.
  intros f s t mc n prevlen nextlen count mx mn Hmn. intros. cbn [send_tree_loop].
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((count + 1 <? mx) && (nextlen =? Len s t (n + 1))); [reflexivity|].
  unfold st_calls.
  destruct (Z.ltb_spec (count + 1) mn) as [C1|C1].
  - destruct (Z_le_gt_dec 0 count).
    + rewrite (send_tree_rep_sbs (Z.to_nat (count + 1)) s nextlen (count + 1)) by lia. reflexivity.
    +
      replace (Z.to_nat (count + 1)) with 0%nat by lia. reflexivity.
  - destruct (negb (nextlen =? 0)).
    + unfold send_dcode, blc. destruct (negb (nextlen =? prevlen)); cbn [sbs_run app]; rewrite ?sb_Code, ?sb_Len; reflexivity.
    + unfold send_dcode, blc. destruct (count + 1 <=? 10); cbn [sbs_run]; reflexivity.
Qed.

Lemma send_loop_0 : forall s t mc n p q c mx mn, send_tree_loop 0 s t mc n p q c mx mn = s.
Proof. reflexivity. Qed.
Lemma send_loop_out : forall f s t mc n p q c mx mn, mc < n -> send_tree_loop f s t mc n p q c mx mn = s.
Proof.
  intros [|f] s t mc n p q c mx mn H; [reflexivity|]. cbn [send_tree_loop].
  destruct (Z.leb_spec n mc); [lia | reflexivity].
Qed.

Fixpoint send_tree_ok (PBL : Z) (fuel : nat) (s : deflate_state) (t : tree_id) (mc n : Z)
         (prevlen nextlen count mx mn : Z) : Prop :=
  match fuel with
  | O => True
  | S f =>
      if n <=? mc then
        let curlen := nextlen in
        let nextlen' := Len s t (n + 1) in
        let count' := count + 1 in
        if (count' <? mx) && (curlen =? nextlen') then
          send_tree_ok PBL f s t mc (n + 1) prevlen nextlen' count' mx mn
        else
          let cs := st_calls s mn curlen prevlen count' in
          let '(mx', mn') := tree_counts curlen nextlen' in
          sbs_ok PBL s cs
          /\ send_tree_ok PBL f (sbs_run s cs) t mc (n + 1) curlen nextlen' 0 mx' mn'
      else True
  end.

Lemma send_loop_tree_fc : forall f s t mc n p q c mx mn t', 1 <= mn ->
  tree_fc (send_tree_loop f s t mc n p q c mx mn) t' = tree_fc s t'
  /\ tree_dl (send_tree_loop f s t mc n p q c mx mn) t' = tree_dl s t'
  /\ arr_len (ds_pending_buf (send_tree_loop f s t mc n p q c mx mn)) = arr_len (ds_pending_buf s)
  /\ (tree_lens s -> tree_lens (send_tree_loop f s t mc n p q c mx mn)).
Proof.
  induction f as [|f IH]; intros s t mc n p q c mx mn t' Hmn; [cbn; tauto|].
  rewrite send_loop_S by exact Hmn.
  destruct (n <=? mc); [|tauto]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:E.
  pose proof (tree_counts_range _ _ _ _ E) as [_ Hmn'].
  destruct (IH (sbs_run s (st_calls s mn q p (c + 1))) t mc (n + 1) q (Len s t (n + 1)) 0 mx' mn' t' ltac:(lia))
    as (A & B & C & D).
  rewrite A, B, C, sbs_tree_fc, sbs_tree_dl, sbs_pbl.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros HL0. apply D. apply sbs_lens. exact HL0.
Qed.
