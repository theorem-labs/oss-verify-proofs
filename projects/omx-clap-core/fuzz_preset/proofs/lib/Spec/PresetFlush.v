(* omx-clap-core/fuzz_preset: P8 part D4 -- the bytes the writer chains free (the flush at RT2 / RT3), over the Spec
   models.

   At a round trip the quarantine's 768-class content is bounded by QT minus the bytes freed after the last big tree
   free: the flush F. At RT3 F is pj_write (copy, 1)'s buffer chain; at RT2 pj_write (doc, 1)'s chain and rendered
   (doc, 1)'s tx_put chain. This file says what F is, from the chain models of PresetReqAt.v (wcaps / w_evs, rcaps /
   r_evs, chain) and the freed requests of PresetRun.v (hfrees, hfrees_w_evs, hfrees_r_evs).

   WHAT IS PROVED.
   - pj_write's chain (WriterSpec.grow_calls over the pieces WriterValue.wdpieces), every grant given:
       wcaps_pow        each capacity is 4096 * 2 ^ j;
       wcaps_last       the last capacity is pow4k (wlen t p + 1), the smallest 4096 * 2 ^ j >= wlen t p + 1;
       w_flush_ge       its frees sum to at least pow4k (wlen t p + 1) - max 4096 (3 * maxpiece t p);
       w_flush_nopiece  with no piece of 4096 bytes or more, at least pow4k (wlen t p + 1) - 4096.
     The last three need wlen t p + 1 <= 2 ^ 76: newcap doubles at most 64 times, so past 4096 * 2 ^ 64 bytes the
     capacities are not the smallest powers. A piece that skips doublings costs up to 3 times its length, not 2: the
     skipped capacities (< 2 * the piece) plus the capacity before the skip, which is below the piece. The
     2 * maxpiece + 8192 shape is false (w_flush_ge_target_false).
   - rendered ()'s chain (PresetReqAt.tx_caps over 0 :: tx_val p 0 t ++ [1 if pretty], no HEAD):
       rpieces_len      its puts sum to wlen t p: rendered's text is the writer's;
       r_flush_calls    its frees sum to at least wlen - 1 - 2 * rmaxpiece * (number of reallocs - 1);
       rcaps_len        the number of reallocs is at most log2 (wlen + 2);
       r_flush_ge       so its frees sum to at least wlen - 1 - 2 * rmaxpiece * (log2 (wlen + 2) - 1).
     A realloc of the buffer holding n bytes for a put of k (to (n + k + 1) * 2) can add up to 2 * k to the gap
     between the capacity and the bytes freed before it, so the term grows with the number of reallocs, at most
     log2 of the length; the depth does not enter (the indentation is put 2 bytes at a time). rmaxpiece is the
     largest tx_put; rmaxpiece_le bounds it by the input.
   - maxpiece_le, rmaxpiece_le: the largest piece is at most max 6 (length x) for a tree read from x. The 6 is the
     \u00XX escape of a control character the input wrote as \b or \f: "\b" (4 bytes) reads to JStr [8], whose piece
     is 6 bytes, so the bound length x is false (maxpiece_le_target_false).
   - parse_frees17: an accepted parse of the writer's text of t frees at most nc9 t + nk65 t requests in 449..640:
     the kids array of a container grown from 8 slots (448 + 16) and the keys array of an object grown from 64 slots
     (512 + 16).

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
  WriterSpec WriterValue PjWriteHyp SlotSizes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss PresetRun.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ definitions *)

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

(* the largest single put of pj_write t p *)
Definition maxpiece (t : jv) (p : bool) : Z := fold_right Z.max 0 (piece_lens (wdpieces t p)).

(* the smallest c * 2 ^ j at least n, j <= fuel *)
Fixpoint pow4k_from (c n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => c
  | S f => if n <=? c then c else pow4k_from (2 * c) n f
  end.

(* the smallest 4096 * 2 ^ j at least n (j <= 64, as newcap) *)
Definition pow4k (n : Z) : Z := pow4k_from 4096 n 64.

(* rendered (t, p)'s puts after its first (empty) one, and the largest *)
Definition rpieces (t : jv) (p : bool) : list Z := tx_val p 0 t ++ (if p then [1] else []).
Definition rmaxpiece (t : jv) (p : bool) : Z := fold_right Z.max 0 (rpieces t p).

(* ================================================================ list facts *)

Lemma zsum_nil : zsum [] = 0.
Proof. reflexivity. Qed.

Lemma zsum_cons : forall a l, zsum (a :: l) = a + zsum l.
Proof. reflexivity. Qed.

Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a as [|x a IH]; intros b; [reflexivity|]. cbn [app]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_nonneg : forall l, Forall (fun z => 0 <= z) l -> 0 <= zsum l.
Proof. intros l H. induction H as [|x l Hx _ IH]; [cbn; lia|]. rewrite zsum_cons. lia. Qed.

Lemma zsum_hd : forall l, zsum (map (fun c => c + HEAD) l) = zsum l + HEAD * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; [cbn; lia|]. cbn [map length]. rewrite !zsum_cons, IH. unfold HEAD. lia.
Qed.

Lemma fmax_nonneg : forall l, 0 <= fold_right Z.max 0 l.
Proof. induction l as [|x l IH]; cbn [fold_right]; lia. Qed.

Lemma fmax_ge : forall l, Forall (fun z => z <= fold_right Z.max 0 l) l.
Proof.
  induction l as [|x l IH]; [constructor|]. cbn [fold_right]. constructor; [lia|].
  eapply Forall_impl; [|exact IH]. intros z Hz. cbv beta in *. lia.
Qed.

Lemma fmax_le : forall l B, 0 <= B -> Forall (fun z => z <= B) l -> fold_right Z.max 0 l <= B.
Proof. intros l B HB H. induction H as [|x l Hx _ IH]; cbn [fold_right]; lia. Qed.

Lemma last_cons2 : forall (a b : Z) r d, last (a :: b :: r) d = last (b :: r) d.
Proof. reflexivity. Qed.

Lemma removelast_cons2 : forall (a b : Z) r, removelast (a :: b :: r) = a :: removelast (b :: r).
Proof. reflexivity. Qed.

Lemma piece_lens_cons : forall b P, piece_lens (b :: P) = Z.of_nat (length b) :: piece_lens P.
Proof. reflexivity. Qed.

Lemma piece_lens_nng : forall P, Forall (fun z => 0 <= z) (piece_lens P).
Proof. induction P as [|b P IH]; [constructor|]. rewrite piece_lens_cons. constructor; [lia | exact IH]. Qed.

Lemma zsum_piece_lens : forall P, zsum (piece_lens P) = Z.of_nat (length (concat P)).
Proof.
  induction P as [|b P IH]; [reflexivity|].
  rewrite piece_lens_cons, zsum_cons, IH, concat_cons, length_app. lia.
Qed.

Lemma wlen_eq : forall t p, wlen t p = zsum (piece_lens (wdpieces t p)).
Proof. intros t p. unfold wlen, wdoc. rewrite zsum_piece_lens. reflexivity. Qed.

Lemma wdpieces_cons : forall t p, exists b P, wdpieces t p = b :: P.
Proof.
  intros t p. unfold wdpieces.
  assert (Hne : exists u pr, wvpieces t p 0 = u :: pr).
  { destruct t; cbn [wvpieces]; eexists; eexists; reflexivity. }
  destruct Hne as (u & pr & Hu). rewrite Hu. exists u, (pr ++ (if p then [[10]] else [])). reflexivity.
Qed.

Lemma pow2_pred : forall j, 1 <= j -> 2 ^ j = 2 * 2 ^ (j - 1).
Proof. intros j H. rewrite <- Z.pow_succ_r by lia. f_equal. lia. Qed.

(* ================================================================ newcap's doubling (WriterSpec.dbl) *)

Lemma pow4k_dbl : forall f c n, pow4k_from c n f = dbl f c n.
Proof. induction f as [|f IH]; intros c n; [reflexivity|]. cbn [pow4k_from dbl]. rewrite IH. reflexivity. Qed.

Lemma dbl_ge : forall f c need, 0 <= c -> c <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (need <=? c); cbv beta iota; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma dbl_stop : forall f c need, need <= c -> dbl f c need = c.
Proof. intros [|f] c need H; cbn [dbl]; [reflexivity|]. rewrite (proj2 (Z.leb_le need c) H). reflexivity. Qed.

Lemma dbl_double : forall f c need, c < need -> need <= 2 * c -> dbl (S f) c need = 2 * c.
Proof.
  intros f c need H1 H2. cbn [dbl]. rewrite (proj2 (Z.leb_gt need c) H1). cbv beta iota.
  apply dbl_stop. exact H2.
Qed.

Lemma dbl_reach : forall f c need, 0 < c -> need <= c * 2 ^ Z.of_nat f -> need <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc H; cbn [dbl].
  - change (Z.of_nat 0) with 0 in H. rewrite Z.pow_0_r in H. lia.
  - destruct (need <=? c) eqn:E; cbv beta iota; [apply Z.leb_le in E; lia|].
    apply IH; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia. nia.
Qed.

Lemma dbl_lt2 : forall f c need, 0 < c -> c < dbl f c need -> dbl f c need < 2 * need.
Proof.
  induction f as [|f IH]; intros c need Hc H; cbn [dbl] in *; [lia|].
  revert H. destruct (need <=? c) eqn:E; cbv beta iota; intros H; [lia|]. apply Z.leb_gt in E.
  destruct (Z.eq_dec (dbl f (2 * c) need) (2 * c)) as [Q|Q].
  - rewrite Q. lia.
  - apply IH; [lia|]. pose proof (dbl_ge f (2 * c) need ltac:(lia)). lia.
Qed.

Lemma dbl_pow : forall f c need, exists j, 0 <= j /\ dbl f c need = c * 2 ^ j.
Proof.
  induction f as [|f IH]; intros c need; cbn [dbl].
  - exists 0. split; [lia|]. rewrite Z.pow_0_r. lia.
  - destruct (need <=? c); cbv beta iota.
    + exists 0. split; [lia|]. rewrite Z.pow_0_r. lia.
    + destruct (IH (2 * c) need) as (j & Hj & E). exists (j + 1). split; [lia|].
      rewrite E, Z.pow_add_r, Z.pow_1_r by lia. ring.
Qed.

(* the doubling from c stops at the smallest c * 2 ^ j at least n *)
Lemma dbl_exact : forall f c n j, 0 < c -> 0 <= j -> j <= Z.of_nat f -> n <= c * 2 ^ j ->
  (j = 0 \/ c * 2 ^ (j - 1) < n) -> dbl f c n = c * 2 ^ j.
Proof.
  induction f as [|f IH]; intros c n j Hc Hj Hf Hn Hm.
  - assert (j = 0) by lia. subst j. cbn [dbl]. rewrite Z.pow_0_r. lia.
  - cbn [dbl]. destruct (n <=? c) eqn:E; cbv beta iota.
    + apply Z.leb_le in E. destruct (Z.eq_dec j 0) as [-> | Hj0]; [rewrite Z.pow_0_r; lia|].
      exfalso. destruct Hm as [Hm|Hm]; [lia|].
      assert (0 < 2 ^ (j - 1)) by (apply Z.pow_pos_nonneg; lia). nia.
    + apply Z.leb_gt in E. destruct (Z.eq_dec j 0) as [-> | Hj0].
      * rewrite Z.pow_0_r in Hn. lia.
      * rewrite (pow2_pred j) in Hn |- * by lia.
        replace (c * (2 * 2 ^ (j - 1))) with (2 * c * 2 ^ (j - 1)) in Hn |- * by ring.
        apply IH; [lia | lia | lia | exact Hn |].
        destruct Hm as [Hm|Hm]; [lia|].
        destruct (Z.eq_dec (j - 1) 0) as [E1|E1]; [left; exact E1|right].
        rewrite (pow2_pred (j - 1)) in Hm by lia. nia.
Qed.

Lemma dbl64_reach : forall c need, 4096 <= c -> need <= 2 ^ 76 -> need <= dbl 64 c need.
Proof.
  intros c need Hc Hn. apply dbl_reach; [lia|]. change (Z.of_nat 64) with 64.
  assert (E : 2 ^ 76 = 4096 * 2 ^ 64) by reflexivity.
  assert (P : 0 <= 2 ^ 64) by (apply Z.pow_nonneg; lia).
  assert (Q : 4096 * 2 ^ 64 <= c * 2 ^ 64) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Lemma pow4k_small : forall n, n <= 4096 -> pow4k n = 4096.
Proof. intros n H. unfold pow4k. rewrite pow4k_dbl. apply dbl_stop. exact H. Qed.

(* ================================================================ pj_write's capacities *)

Definition ispow (c : Z) : Prop := exists j, 0 <= j /\ c = 4096 * 2 ^ j.

Lemma ispow_ge : forall c, ispow c -> 4096 <= c.
Proof. intros c (j & Hj & ->). assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma ispow_dbl : forall f c need, ispow c -> ispow (dbl f c need).
Proof.
  intros f c need (j & Hj & ->). destruct (dbl_pow f (4096 * 2 ^ j) need) as (k & Hk & E).
  exists (j + k). split; [lia|]. rewrite E, Z.pow_add_r by lia. ring.
Qed.

Lemma newcap_nz : forall c need, c <> 0 -> newcap c need = dbl 64 c need.
Proof. intros c need H. unfold newcap. rewrite (proj2 (Z.eqb_neq c 0) H). reflexivity. Qed.

Lemma newcap_0 : forall need, newcap 0 need = pow4k need.
Proof. intros need. unfold newcap, pow4k. rewrite pow4k_dbl. reflexivity. Qed.

Lemma ispow_newcap : forall c need, c = 0 \/ ispow c -> ispow (newcap c need).
Proof.
  intros c need [-> | H].
  - rewrite newcap_0. unfold pow4k. rewrite pow4k_dbl. apply ispow_dbl. exists 0. split; [lia | reflexivity].
  - rewrite newcap_nz by (pose proof (ispow_ge c H); lia). apply ispow_dbl. exact H.
Qed.

Lemma gc_pow : forall ls x c, c = 0 \/ ispow c -> Forall ispow (grow_calls x c ls).
Proof.
  induction ls as [|l ls IH]; intros x c H; cbn [grow_calls]; [constructor|].
  destruct (c <? x + l + 1); cbv beta iota.
  - constructor; [apply ispow_newcap; exact H|]. apply IH. right. apply ispow_newcap. exact H.
  - apply IH. exact H.
Qed.

(* the state after a piece: x bytes written into the capacity c, the smallest 4096 * 2 ^ j above them *)
Definition winv (x c : Z) : Prop := 0 <= x /\ x + 1 <= c /\ (c = 4096 \/ c < 2 * (x + 1)) /\ ispow c.

Lemma winv_first : forall l, 0 <= l -> l + 1 <= 2 ^ 76 -> winv l (pow4k (l + 1)).
Proof.
  intros l Hl Hb. unfold pow4k. rewrite pow4k_dbl.
  pose proof (dbl64_reach 4096 (l + 1) ltac:(lia) Hb) as Hr.
  split; [lia|]. split; [lia|]. split.
  - destruct (Z.eq_dec (dbl 64 4096 (l + 1)) 4096) as [Q|Q]; [left; exact Q|right].
    apply dbl_lt2; [lia|]. pose proof (dbl_ge 64 4096 (l + 1) ltac:(lia)). lia.
  - apply ispow_dbl. exists 0. split; [lia | reflexivity].
Qed.

Lemma winv_step : forall x c l, winv x c -> 0 <= l -> x + l + 1 <= 2 ^ 76 -> c < x + l + 1 ->
  winv (x + l) (newcap c (x + l + 1)).
Proof.
  intros x c l (Hx & Hc1 & Hc2 & Hp) Hl Hb Hlt.
  pose proof (ispow_ge c Hp) as Hc4.
  rewrite newcap_nz by lia.
  pose proof (dbl64_reach c (x + l + 1) Hc4 Hb) as Hr.
  split; [lia|]. split; [lia|]. split.
  - right. apply (dbl_lt2 64 c); lia.
  - apply ispow_dbl. exact Hp.
Qed.

Lemma winv_keep : forall x c l, winv x c -> 0 <= l -> x + l + 1 <= c -> winv (x + l) c.
Proof. intros x c l (Hx & Hc1 & Hc2 & Hp) Hl H. split; [lia|]. split; [lia|]. split; [lia | exact Hp]. Qed.

Lemma winv_pow4k : forall x c, winv x c -> x + 1 <= 2 ^ 76 -> c = pow4k (x + 1).
Proof.
  intros x c (Hx & Hc1 & Hc2 & j & Hj & ->) Hb. unfold pow4k. rewrite pow4k_dbl.
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  symmetry. apply dbl_exact; [lia | exact Hj | | lia | ].
  - change (Z.of_nat 64) with 64. destruct (Z.le_gt_cases j 64) as [H|H]; [exact H|exfalso].
    destruct Hc2 as [Hc2|Hc2].
    + assert (H2 : 2 ^ 1 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). rewrite Z.pow_1_r in H2. lia.
    + assert (E : 2 ^ 76 = 4096 * 2 ^ 64) by reflexivity.
      assert (H2 : 2 ^ 64 <= 2 ^ (j - 1)) by (apply Z.pow_le_mono_r; lia).
      rewrite (pow2_pred j) in Hc2 by lia. lia.
  - destruct (Z.eq_dec j 0) as [E|E]; [left; exact E|right].
    destruct Hc2 as [Hc2|Hc2].
    + exfalso. assert (H2 : 2 ^ 1 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). rewrite Z.pow_1_r in H2. lia.
    + rewrite (pow2_pred j) in Hc2 by lia. lia.
Qed.

Lemma gc_last : forall ls x c, winv x c -> Forall (fun l => 0 <= l) ls -> x + zsum ls + 1 <= 2 ^ 76 ->
  winv (x + zsum ls) (last (c :: grow_calls x c ls) 0).
Proof.
  induction ls as [|l ls IH]; intros x c Hw Hl Hb.
  - cbn [grow_calls last]. rewrite zsum_nil, Z.add_0_r. exact Hw.
  - apply Forall_cons_iff in Hl as [Hl0 Hls]. pose proof (zsum_nonneg ls Hls) as Z0.
    rewrite zsum_cons in *. cbn [grow_calls].
    replace (x + (l + zsum ls)) with (x + l + zsum ls) by lia.
    destruct (c <? x + l + 1) eqn:E; cbv beta iota.
    + apply Z.ltb_lt in E. rewrite last_cons2.
      apply IH; [apply winv_step; [exact Hw | lia | lia | exact E] | exact Hls | lia].
    + apply Z.ltb_ge in E.
      apply IH; [apply winv_keep; [exact Hw | lia | exact E] | exact Hls | lia].
Qed.

(* the frees of the chain from state (x, c) on: Sm is what the capacities before c summed to *)
Lemma gc_flush : forall ls x c Sm M B, winv x c -> Forall (fun l => 0 <= l <= M) ls -> x + zsum ls + 1 <= 2 ^ 76 ->
  0 <= Sm -> c - Sm <= B -> (4096 <= M -> 3 * M <= B) ->
  last (c :: grow_calls x c ls) 0 - B <= Sm + zsum (removelast (c :: grow_calls x c ls)).
Proof.
  induction ls as [|l ls IH]; intros x c Sm M B Hw Hl Hb HS HB HM.
  - cbn [grow_calls last removelast]. rewrite zsum_nil. lia.
  - apply Forall_cons_iff in Hl as [Hl0 Hls].
    assert (Z0 : 0 <= zsum ls)
      by (apply zsum_nonneg; eapply Forall_impl; [|exact Hls]; intros z Hz; cbv beta in *; lia).
    rewrite zsum_cons in Hb. cbn [grow_calls].
    destruct (c <? x + l + 1) eqn:E; cbv beta iota.
    + apply Z.ltb_lt in E. rewrite last_cons2, removelast_cons2, zsum_cons.
      set (c' := newcap c (x + l + 1)).
      assert (Hw' : winv (x + l) c') by (apply winv_step; [exact Hw | lia | lia | exact E]).
      assert (Hd : c' - (Sm + c) <= B).
      { destruct Hw as (Hx & Hc1 & Hc2 & Hp). pose proof (ispow_ge c Hp) as Hc4.
        unfold c'. rewrite newcap_nz by lia.
        destruct (Z.le_gt_cases (x + l + 1) (2 * c)) as [Hn|Hn].
        - rewrite (dbl_double 63 c (x + l + 1)) by lia. lia.
        - pose proof (dbl64_reach c (x + l + 1) Hc4 ltac:(lia)) as Hr.
          pose proof (dbl_lt2 64 c (x + l + 1) ltac:(lia) ltac:(lia)) as H2.
          specialize (HM ltac:(lia)). lia. }
      assert (Hc0 : 0 <= c) by (destruct Hw as (Hx & Hc1 & _); lia).
      specialize (IH (x + l) c' (Sm + c) M B Hw' Hls ltac:(lia) ltac:(lia) Hd HM). lia.
    + apply Z.ltb_ge in E.
      apply (IH (x + l) c Sm M B);
        [apply winv_keep; [exact Hw | lia | exact E] | exact Hls | lia | exact HS | exact HB | exact HM].
Qed.

Lemma wcaps_split : forall t p, exists l rest,
  piece_lens (wdpieces t p) = l :: rest /\ wcaps t p = pow4k (l + 1) :: grow_calls l (pow4k (l + 1)) rest.
Proof.
  intros t p. destruct (wdpieces_cons t p) as (b & P & E).
  exists (Z.of_nat (length b)), (piece_lens P). unfold wcaps. rewrite E, piece_lens_cons. split; [reflexivity|].
  cbn [grow_calls]. rewrite (proj2 (Z.ltb_lt 0 (0 + Z.of_nat (length b) + 1))) by lia.
  rewrite newcap_0, !Z.add_0_l. reflexivity.
Qed.

(* ---------------------------------------------------------------- the theorems *)

Theorem wcaps_pow : forall t p, Forall (fun c => exists j, 0 <= j /\ c = 4096 * 2 ^ j) (wcaps t p).
Proof. intros t p. exact (gc_pow (piece_lens (wdpieces t p)) 0 0 (or_introl eq_refl)). Qed.

Theorem wcaps_last : forall t p, wlen t p + 1 <= 2 ^ 76 -> last (wcaps t p) 0 = pow4k (wlen t p + 1).
Proof.
  intros t p Hb. destruct (wcaps_split t p) as (l & rest & Ep & Ew). rewrite Ew.
  pose proof (piece_lens_nng (wdpieces t p)) as Hn. rewrite Ep in Hn. apply Forall_cons_iff in Hn as [Hl Hr].
  rewrite wlen_eq, Ep, zsum_cons in Hb |- *.
  pose proof (zsum_nonneg rest Hr) as Z0.
  pose proof (gc_last rest l (pow4k (l + 1)) (winv_first l Hl ltac:(lia)) Hr ltac:(lia)) as H.
  exact (winv_pow4k _ _ H ltac:(lia)).
Qed.

Lemma w_flush_gen : forall t p B, wlen t p + 1 <= 2 ^ 76 ->
  (forall l, 0 <= l <= maxpiece t p -> winv l (pow4k (l + 1)) -> pow4k (l + 1) <= B) ->
  (4096 <= maxpiece t p -> 3 * maxpiece t p <= B) ->
  zsum (hfrees (w_evs t p)) >= pow4k (wlen t p + 1) - B.
Proof.
  intros t p B Hb H1 H3.
  rewrite hfrees_w_evs, zsum_hd, <- (wcaps_last t p Hb).
  assert (HM : Forall (fun z => 0 <= z <= maxpiece t p) (piece_lens (wdpieces t p))).
  { pose proof (piece_lens_nng (wdpieces t p)) as A. pose proof (fmax_ge (piece_lens (wdpieces t p))) as Bm.
    rewrite Forall_forall in A, Bm |- *. intros z Hz. split; [exact (A z Hz) | exact (Bm z Hz)]. }
  destruct (wcaps_split t p) as (l & rest & Ep & Ew). rewrite Ew.
  rewrite Ep in HM. apply Forall_cons_iff in HM as [Hl Hr].
  rewrite wlen_eq, Ep, zsum_cons in Hb.
  assert (Z0 : 0 <= zsum rest)
    by (apply zsum_nonneg; eapply Forall_impl; [|exact Hr]; intros z Hz; cbv beta in *; lia).
  pose proof (winv_first l ltac:(lia) ltac:(lia)) as W1.
  pose proof (H1 l Hl W1) as Hc1.
  pose proof (gc_flush rest l (pow4k (l + 1)) 0 (maxpiece t p) B W1 Hr ltac:(lia) ltac:(lia) ltac:(lia) H3) as H.
  pose proof (Zle_0_nat (length (removelast (pow4k (l + 1) :: grow_calls l (pow4k (l + 1)) rest)))).
  unfold HEAD. lia.
Qed.

Theorem w_flush_ge : forall t p, wlen t p + 1 <= 2 ^ 76 ->
  zsum (hfrees (w_evs t p)) >= pow4k (wlen t p + 1) - Z.max 4096 (3 * maxpiece t p).
Proof.
  intros t p Hb. apply w_flush_gen; [exact Hb | | lia].
  intros l Hl (_ & _ & Hc & _). lia.
Qed.

Theorem w_flush_nopiece : forall t p, wlen t p + 1 <= 2 ^ 76 -> maxpiece t p < 4096 ->
  zsum (hfrees (w_evs t p)) >= pow4k (wlen t p + 1) - 4096.
Proof.
  intros t p Hb Hm. apply w_flush_gen; [exact Hb | | lia].
  intros l Hl _. rewrite pow4k_small by lia. lia.
Qed.

(* The target shape (2 * maxpiece + 8192) is false: "[" 16381 bytes "," 49153 bytes "]" grows 4096 -> 16384 ->
   131072 and frees 4112 + 16400 = 20512 < 131072 - 2 * 49153 - 8192 = 24574. *)
Definition cex_w : jv := JArr [JNum (repeat 49 (Z.to_nat 16381)) 0; JNum (repeat 49 (Z.to_nat 49153)) 0].

Example w_flush_ge_target_false :
  wlen cex_w false + 1 <= 2 ^ 76 /\
  zsum (hfrees (w_evs cex_w false)) < pow4k (wlen cex_w false + 1) - 2 * maxpiece cex_w false - 8192.
Proof. split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

(* ================================================================ rendered ()'s chain *)

Lemma zsum_rep2 : forall n, zsum (repeat 2 n) = 2 * Z.of_nat n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat]. rewrite zsum_cons, IH. lia. Qed.

Lemma zsum_ind : forall (p : bool) (d : nat), zsum (if p then tx_line d else []) = indl p d.
Proof.
  intros [|] d; unfold indl; cbv beta iota; [|reflexivity].
  unfold tx_line. rewrite zsum_cons, zsum_rep2. reflexivity.
Qed.

Lemma tx_ch_len : forall c, zsum (tx_ch c) = Z.of_nat (length (ech c)).
Proof.
  intros c. unfold tx_ch, ech, special, esc.
  destruct (c =? 34); [reflexivity|]. cbn [orb].
  destruct (c =? 92); [reflexivity|]. cbn [orb].
  rewrite Z.ltb_antisym. destruct (32 <=? c); [reflexivity|]. cbn [negb].
  destruct (c =? 10); [reflexivity|]. destruct (c =? 9); [reflexivity|]. destruct (c =? 13); reflexivity.
Qed.

Lemma tx_str_len : forall s, zsum (tx_str s) = Z.of_nat (length (concat (spieces s))).
Proof.
  intros s. rewrite wstr_eq. unfold tx_str. rewrite zsum_cons, zsum_app, zsum_cons, zsum_nil.
  cbn [length]. rewrite length_app. cbn [length].
  assert (H : zsum (flat_map tx_ch s) = Z.of_nat (length (flat_map ech s))).
  { induction s as [|c s IH]; [reflexivity|]. cbn [flat_map]. rewrite zsum_app, length_app, IH, tx_ch_len. lia. }
  lia.
Qed.

Lemma tx_len : forall t p d, zsum (tx_val p d t) = Z.of_nat (length (concat (wvpieces t p (Z.of_nat d)))).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros p d.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [tx_val wvpieces concat]. rewrite app_nil_r, zsum_cons, zsum_nil. lia.
  - cbn [tx_val wvpieces]. apply tx_str_len.
  - rewrite tx_arr_eq, wv_arr.
    assert (Hgo : forall l i, Forall (fun u => forall p' d',
        zsum (tx_val p' d' u) = Z.of_nat (length (concat (wvpieces u p' (Z.of_nat d'))))) l ->
      zsum (txa p d i l) = Z.of_nat (length (concat (wgo_arr p (Z.of_nat d) i l)))).
    { induction l as [|u r IHl]; intros i Hf; [reflexivity|].
      apply Forall_cons_iff in Hf as [Hu Hr]. cbn [txa wgo_arr].
      rewrite !zsum_app, !concat_app, !length_app.
      replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
      rewrite (Hu p (S d)), (IHl (S i) Hr), zsum_ind.
      pose proof (wind_len p (S d)) as W.
      assert (C : zsum (if Nat.eqb i 0 then [] else [1]) = Z.of_nat (length (concat (wcomma i))))
        by (unfold wcomma; destruct (Nat.eqb i 0); reflexivity).
      lia. }
    rewrite zsum_cons, !zsum_app, concat_cons, !concat_app, !length_app, (Hgo items 0%nat IH).
    assert (C : zsum (match items with [] => [] | _ :: _ => if p then tx_line d else [] end) =
                Z.of_nat (length (concat (match items with [] => [] | _ :: _ => wind p (Z.of_nat d) end)))).
    { destruct items; [reflexivity|]. rewrite zsum_ind, wind_len. reflexivity. }
    rewrite zsum_cons, zsum_nil. cbn [length concat app]. lia.
  - rewrite tx_obj_eq, wv_obj.
    assert (Hgo : forall l i, Forall (fun m => forall p' d',
        zsum (tx_val p' d' (snd m)) = Z.of_nat (length (concat (wvpieces (snd m) p' (Z.of_nat d'))))) l ->
      zsum (txo p d i l) = Z.of_nat (length (concat (wgo_obj p (Z.of_nat d) i l)))).
    { induction l as [|[k u] r IHl]; intros i Hf; [reflexivity|].
      apply Forall_cons_iff in Hf as [Hu Hr]. cbn [snd] in Hu. cbn [txo wgo_obj].
      rewrite !zsum_app, !concat_app, !length_app.
      replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
      rewrite (Hu p (S d)), (IHl (S i) Hr), zsum_ind, tx_str_len.
      pose proof (wind_len p (S d)) as W.
      assert (C : zsum (if Nat.eqb i 0 then [] else [1]) = Z.of_nat (length (concat (wcomma i))))
        by (unfold wcomma; destruct (Nat.eqb i 0); reflexivity).
      assert (C2 : zsum [1] + zsum (if p then [1] else []) = Z.of_nat (length (concat [wsep p])))
        by (destruct p; reflexivity).
      lia. }
    rewrite zsum_cons, !zsum_app, concat_cons, !concat_app, !length_app, (Hgo ms 0%nat IH).
    assert (C : zsum (match ms with [] => [] | _ :: _ => if p then tx_line d else [] end) =
                Z.of_nat (length (concat (match ms with [] => [] | _ :: _ => wind p (Z.of_nat d) end)))).
    { destruct ms; [reflexivity|]. rewrite zsum_ind, wind_len. reflexivity. }
    rewrite zsum_cons, zsum_nil. cbn [length concat app]. lia.
Qed.

(* rendered (t, p)'s text is as long as the writer's *)
Theorem rpieces_len : forall t p, zsum (rpieces t p) = Z.of_nat (length (wdoc t p)).
Proof.
  intros t p. unfold rpieces, wdoc, wdpieces.
  pose proof (tx_len t p 0%nat) as E. change (Z.of_nat 0) with 0 in E.
  rewrite zsum_app, concat_app, length_app, E.
  destruct p; cbv beta iota; rewrite ?zsum_cons, ?zsum_nil; cbn [concat app length]; lia.
Qed.

Lemma rpieces_nng : forall t p, Forall (fun k => 0 <= k) (rpieces t p).
Proof.
  intros t p. unfold rpieces. apply Forall_app. split; [exact (nng_tx_val t p 0%nat)|].
  destruct p; [constructor; [lia | constructor] | constructor].
Qed.

Lemma rcaps_eq : forall t p, rcaps t p = 2 :: tx_caps 0 2 (rpieces t p).
Proof. intros t p. reflexivity. Qed.

Lemma tx_last_ge : forall ls n cap, 0 <= n -> n + 1 <= cap -> Forall (fun k => 0 <= k) ls ->
  n + zsum ls + 1 <= last (cap :: tx_caps n cap ls) 0.
Proof.
  induction ls as [|k ls IH]; intros n cap Hn Hc Hl.
  - cbn [tx_caps last]. rewrite zsum_nil. lia.
  - apply Forall_cons_iff in Hl as [Hk Hl]. rewrite zsum_cons. cbn [tx_caps].
    destruct (cap <? n + k + 1) eqn:E; cbv beta iota.
    + apply Z.ltb_lt in E. rewrite last_cons2.
      specialize (IH (n + k) ((n + k + 1) * 2) ltac:(lia) ltac:(lia) Hl). lia.
    + apply Z.ltb_ge in E. specialize (IH (n + k) cap ltac:(lia) ltac:(lia) Hl). lia.
Qed.

Lemma tx_last_le : forall ls n cap, 0 <= n -> 0 <= cap -> Forall (fun k => 0 <= k) ls ->
  last (cap :: tx_caps n cap ls) 0 <= Z.max cap (2 * (n + zsum ls + 1)).
Proof.
  induction ls as [|k ls IH]; intros n cap Hn Hc Hl.
  - cbn [tx_caps last]. lia.
  - apply Forall_cons_iff in Hl as [Hk Hl]. pose proof (zsum_nonneg ls Hl).
    rewrite zsum_cons. cbn [tx_caps].
    destruct (cap <? n + k + 1) eqn:E; cbv beta iota.
    + rewrite last_cons2. specialize (IH (n + k) ((n + k + 1) * 2) ltac:(lia) ltac:(lia) Hl). lia.
    + specialize (IH (n + k) cap ltac:(lia) Hc Hl). lia.
Qed.

(* each realloc more than doubles cap + 2 *)
Lemma tx_count : forall ls n cap, 0 <= n -> n + 1 <= cap -> Forall (fun k => 0 <= k) ls ->
  (cap + 2) * 2 ^ Z.of_nat (length (tx_caps n cap ls)) <= last (cap :: tx_caps n cap ls) 0 + 2.
Proof.
  induction ls as [|k ls IH]; intros n cap Hn Hc Hl.
  - cbn [tx_caps last length]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. lia.
  - apply Forall_cons_iff in Hl as [Hk Hl]. cbn [tx_caps].
    destruct (cap <? n + k + 1) eqn:E; cbv beta iota.
    + apply Z.ltb_lt in E. rewrite last_cons2. cbn [length].
      specialize (IH (n + k) ((n + k + 1) * 2) ltac:(lia) ltac:(lia) Hl).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      set (X := 2 ^ Z.of_nat (length (tx_caps (n + k) ((n + k + 1) * 2) ls))) in *.
      assert (P : 0 < X) by (unfold X; apply Z.pow_pos_nonneg; lia).
      assert (2 * (cap + 2) <= (n + k + 1) * 2 + 2) by lia.
      nia.
    + apply Z.ltb_ge in E. apply IH; [lia | lia | exact Hl].
Qed.

(* each realloc can leave cap short of the bytes before it by at most 2 * (the put + 1) more *)
Lemma tx_flush : forall ls n cap Sm j K, 0 <= n -> n + 1 <= cap -> 0 <= K ->
  Forall (fun k => 0 <= k <= K) ls -> cap - Sm <= 2 + 2 * K * j ->
  last (cap :: tx_caps n cap ls) 0 - 2 - 2 * K * (j + Z.of_nat (length (tx_caps n cap ls)))
    <= Sm + zsum (removelast (cap :: tx_caps n cap ls)).
Proof.
  induction ls as [|k ls IH]; intros n cap Sm j K Hn Hc HK Hl HS.
  - cbn [tx_caps last removelast length]. rewrite zsum_nil. nia.
  - apply Forall_cons_iff in Hl as [Hk Hl]. cbn [tx_caps].
    destruct (cap <? n + k + 1) eqn:E; cbv beta iota.
    + apply Z.ltb_lt in E. rewrite last_cons2, removelast_cons2, zsum_cons. cbn [length].
      specialize (IH (n + k) ((n + k + 1) * 2) (Sm + cap) (j + 1) K ltac:(lia) ltac:(lia) HK Hl ltac:(nia)).
      rewrite Nat2Z.inj_succ. nia.
    + apply Z.ltb_ge in E. apply IH; [lia | lia | exact HK | exact Hl | exact HS].
Qed.

Theorem rcaps_len : forall t p, Z.of_nat (length (rcaps t p)) <= Z.log2 (Z.of_nat (length (wdoc t p)) + 2).
Proof.
  intros t p. rewrite <- rpieces_len, rcaps_eq.
  pose proof (rpieces_nng t p) as Hn. pose proof (zsum_nonneg _ Hn) as Z0.
  pose proof (tx_count (rpieces t p) 0 2 ltac:(lia) ltac:(lia) Hn) as Hc.
  pose proof (tx_last_le (rpieces t p) 0 2 ltac:(lia) ltac:(lia) Hn) as Hl.
  set (G := tx_caps 0 2 (rpieces t p)) in *.
  assert (HX : 0 < 2 ^ Z.of_nat (length G)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp : 2 ^ (Z.of_nat (length G) + 1) <= zsum (rpieces t p) + 2).
  { rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
  replace (Z.of_nat (length (2 :: G))) with (Z.of_nat (length G) + 1) by (cbn [length]; lia).
  rewrite <- (Z.log2_pow2 (Z.of_nat (length G) + 1)) by lia. apply Z.log2_le_mono. exact Hp.
Qed.

Theorem r_flush_calls : forall t p, zsum (hfrees (r_evs t p)) >=
  Z.of_nat (length (wdoc t p)) - 1 - 2 * rmaxpiece t p * (Z.of_nat (length (rcaps t p)) - 1).
Proof.
  intros t p. rewrite hfrees_r_evs, <- rpieces_len, rcaps_eq.
  pose proof (rpieces_nng t p) as Hn.
  assert (HK : 0 <= rmaxpiece t p) by (unfold rmaxpiece; apply fmax_nonneg).
  assert (HL : Forall (fun k => 0 <= k <= rmaxpiece t p) (rpieces t p)).
  { pose proof (rpieces_nng t p) as A. pose proof (fmax_ge (rpieces t p)) as B.
    rewrite Forall_forall in A, B |- *. intros z Hz. split; [exact (A z Hz) | exact (B z Hz)]. }
  pose proof (tx_flush (rpieces t p) 0 2 0 0 (rmaxpiece t p) ltac:(lia) ltac:(lia) HK HL ltac:(nia)) as F.
  pose proof (tx_last_ge (rpieces t p) 0 2 ltac:(lia) ltac:(lia) Hn) as G.
  cbn [length]. rewrite Nat2Z.inj_succ. nia.
Qed.

Theorem r_flush_ge : forall t p, zsum (hfrees (r_evs t p)) >=
  Z.of_nat (length (wdoc t p)) - 1 - 2 * rmaxpiece t p * (Z.log2 (Z.of_nat (length (wdoc t p)) + 2) - 1).
Proof.
  intros t p. pose proof (r_flush_calls t p). pose proof (rcaps_len t p).
  assert (0 <= rmaxpiece t p) by (unfold rmaxpiece; apply fmax_nonneg).
  nia.
Qed.

(* ================================================================ the largest piece, from the input *)

Lemma esc_len : forall c, (length (esc c) <= 6)%nat.
Proof.
  intros c. unfold esc.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [length]; lia.
Qed.

Lemma sr_le : forall bs run M, (6 <= M)%nat -> (length run + length bs <= M)%nat ->
  Forall (fun b => (length b <= M)%nat) (spieces_run run bs).
Proof.
  induction bs as [|c bs IH]; intros run M H6 Hl; cbn [spieces_run].
  - cbn [length] in Hl. constructor; [lia | constructor].
  - cbn [length] in Hl. destruct (special c).
    + constructor; [lia|]. constructor; [pose proof (esc_len c); lia|]. apply IH; [lia | cbn [length]; lia].
    + apply IH; [lia|]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma sp_le : forall s M, (6 <= M)%nat -> (length s <= M)%nat -> Forall (fun b => (length b <= M)%nat) (spieces s).
Proof.
  intros s M H6 Hs. unfold spieces. constructor; [cbn [length]; lia|].
  apply Forall_app. split; [apply sr_le; cbn [length]; lia | constructor; [cbn [length]; lia | constructor]].
Qed.

Lemma wind_le : forall p d M, (6 <= M)%nat -> Forall (fun b => (length b <= M)%nat) (wind p d).
Proof.
  intros [|] d M H6; unfold wind; [|constructor].
  constructor; [cbn [length]; lia|]. apply Forall_forall. intros b Hb. apply repeat_spec in Hb. subst b.
  cbn [length]. lia.
Qed.

Lemma wcomma_le : forall i M, (6 <= M)%nat -> Forall (fun b => (length b <= M)%nat) (wcomma i).
Proof. intros i M H6. unfold wcomma. destruct (Nat.eqb i 0); [constructor | constructor; [cbn [length]; lia | constructor]]. Qed.

Lemma wv_le : forall t M p d, (6 <= M)%nat -> tlen M t -> Forall (fun b => (length b <= M)%nat) (wvpieces t p d).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros M p d H6 Ht.
  - cbn [wvpieces]. constructor; [cbn [length]; lia | constructor].
  - cbn [wvpieces]. constructor; [cbn [length]; lia | constructor].
  - cbn [wvpieces]. constructor; [cbn [length]; lia | constructor].
  - cbn [wvpieces]. cbn [tlen] in Ht. constructor; [exact Ht | constructor].
  - cbn [wvpieces]. cbn [tlen] in Ht. apply sp_le; assumption.
  - apply tlen_arr in Ht. rewrite wv_arr. constructor; [cbn [length]; lia|].
    assert (Hgo : forall l i, Forall (fun u => forall M' p' d', (6 <= M')%nat -> tlen M' u ->
        Forall (fun b => (length b <= M')%nat) (wvpieces u p' d')) l ->
      Forall (tlen M) l -> Forall (fun b => (length b <= M)%nat) (wgo_arr p d i l)).
    { induction l as [|u r IHl]; intros i Hf Hl; [constructor|].
      apply Forall_cons_iff in Hf as [Hu Hr]. apply Forall_cons_iff in Hl as [Hlu Hlr]. cbn [wgo_arr].
      apply Forall_app; split; [apply wcomma_le; exact H6|].
      apply Forall_app; split; [apply wind_le; exact H6|].
      apply Forall_app; split; [apply Hu; assumption|]. apply IHl; assumption. }
    apply Forall_app; split; [apply Hgo; assumption|].
    apply Forall_app; split; [destruct items; [constructor | apply wind_le; exact H6]|].
    constructor; [cbn [length]; lia | constructor].
  - apply tlen_obj in Ht. rewrite wv_obj. constructor; [cbn [length]; lia|].
    assert (Hgo : forall l i, Forall (fun m => forall M' p' d', (6 <= M')%nat -> tlen M' (snd m) ->
        Forall (fun b => (length b <= M')%nat) (wvpieces (snd m) p' d')) l ->
      Forall (fun m => (length (fst m) <= M)%nat /\ tlen M (snd m)) l ->
      Forall (fun b => (length b <= M)%nat) (wgo_obj p d i l)).
    { induction l as [|[k u] r IHl]; intros i Hf Hl; [constructor|].
      apply Forall_cons_iff in Hf as [Hu Hr]. apply Forall_cons_iff in Hl as [[Hk Hlu] Hlr].
      cbn [fst snd] in *. cbn [wgo_obj].
      apply Forall_app; split; [apply wcomma_le; exact H6|].
      apply Forall_app; split; [apply wind_le; exact H6|].
      apply Forall_app; split; [apply sp_le; assumption|].
      apply Forall_app; split; [constructor; [unfold wsep; destruct p; cbn [length]; lia | constructor]|].
      apply Forall_app; split; [apply Hu; assumption|]. apply IHl; assumption. }
    apply Forall_app; split; [apply Hgo; assumption|].
    apply Forall_app; split; [destruct ms; [constructor | apply wind_le; exact H6]|].
    constructor; [cbn [length]; lia | constructor].
Qed.

Theorem maxpiece_le : forall sm x t p, json_read sm x = Some t -> maxpiece t p <= Z.max 6 (Z.of_nat (length x)).
Proof.
  intros sm x t p H. pose proof (G12_read_len sm x t H) as Ht.
  set (M := Nat.max 6 (length x)).
  assert (H6 : (6 <= M)%nat) by (unfold M; apply Nat.le_max_l).
  assert (HM : tlen M t) by (apply (tlen_mono t (length x)); [unfold M; apply Nat.le_max_r | exact Ht]).
  assert (HF : Forall (fun b => (length b <= M)%nat) (wdpieces t p)).
  { unfold wdpieces. apply Forall_app. split; [apply wv_le; assumption|].
    destruct p; [constructor; [cbn [length]; lia | constructor] | constructor]. }
  assert (EM : Z.of_nat M = Z.max 6 (Z.of_nat (length x))) by (unfold M; rewrite Nat2Z.inj_max; reflexivity).
  rewrite <- EM. unfold maxpiece. apply fmax_le; [lia|].
  unfold piece_lens. apply Forall_map. eapply Forall_impl; [|exact HF]. intros b Hb. cbv beta in *. lia.
Qed.

(* The target shape (length x) is false: "\b" (4 bytes) reads to JStr [8], written "\u0008" (a 6-byte piece). *)
Example maxpiece_le_target_false : forall sm,
  json_read sm [34; 92; 98; 34] = Some (JStr [8]) /\ maxpiece (JStr [8]) false = 6.
Proof. intros sm. split; vm_compute; reflexivity. Qed.

(* rendered ()'s puts: at most 6, except a number's text *)
Lemma le6M : forall l M, (6 <= M)%nat -> Forall (fun k => k <= 6) l -> Forall (fun k => k <= Z.of_nat M) l.
Proof. intros l M H F. eapply Forall_impl; [|exact F]. intros k Hk. cbv beta in *. lia. Qed.

Lemma tx_line_le : forall d, Forall (fun k => k <= 6) (tx_line d).
Proof.
  intros d. unfold tx_line. constructor; [lia|].
  apply Forall_forall. intros z Hz. apply repeat_spec in Hz. lia.
Qed.

Lemma tx_str_le : forall s, Forall (fun k => k <= 6) (tx_str s).
Proof.
  intros s. unfold tx_str. constructor; [lia|]. apply Forall_app. split; [|constructor; [lia | constructor]].
  induction s as [|c s IH]; [constructor|]. cbn [flat_map]. apply Forall_app. split; [|exact IH].
  unfold tx_ch.
  destruct ((c =? 34) || (c =? 92)); [repeat (apply Forall_cons; [lia|]); apply Forall_nil|].
  destruct (32 <=? c); [repeat (apply Forall_cons; [lia|]); apply Forall_nil|].
  destruct ((c =? 10) || (c =? 9) || (c =? 13)); repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.

Lemma txv_le : forall t M p d, (6 <= M)%nat -> tlen M t -> Forall (fun k => k <= Z.of_nat M) (tx_val p d t).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros M p d H6 Ht.
  - cbn [tx_val]. constructor; [lia | constructor].
  - cbn [tx_val]. constructor; [lia | constructor].
  - cbn [tx_val]. constructor; [lia | constructor].
  - cbn [tx_val]. cbn [tlen] in Ht. constructor; [lia | constructor].
  - cbn [tx_val]. apply le6M; [exact H6 | apply tx_str_le].
  - apply tlen_arr in Ht. rewrite tx_arr_eq. constructor; [lia|].
    assert (Hgo : forall l i, Forall (fun u => forall M' p' d', (6 <= M')%nat -> tlen M' u ->
        Forall (fun k => k <= Z.of_nat M') (tx_val p' d' u)) l ->
      Forall (tlen M) l -> Forall (fun k => k <= Z.of_nat M) (txa p d i l)).
    { induction l as [|u r IHl]; intros i Hf Hl; [constructor|].
      apply Forall_cons_iff in Hf as [Hu Hr]. apply Forall_cons_iff in Hl as [Hlu Hlr]. cbn [txa].
      apply Forall_app; split;
        [apply le6M; [exact H6|]; destruct (Nat.eqb i 0); [constructor | constructor; [lia | constructor]]|].
      apply Forall_app; split; [apply le6M; [exact H6|]; destruct p; [apply tx_line_le | constructor]|].
      apply Forall_app; split; [apply Hu; assumption|]. apply IHl; assumption. }
    apply Forall_app; split; [apply Hgo; assumption|].
    apply Forall_app; split;
      [apply le6M; [exact H6|]; destruct items; [constructor | destruct p; [apply tx_line_le | constructor]]|].
    constructor; [lia | constructor].
  - apply tlen_obj in Ht. rewrite tx_obj_eq. constructor; [lia|].
    assert (Hgo : forall l i, Forall (fun m => forall M' p' d', (6 <= M')%nat -> tlen M' (snd m) ->
        Forall (fun k => k <= Z.of_nat M') (tx_val p' d' (snd m))) l ->
      Forall (fun m => (length (fst m) <= M)%nat /\ tlen M (snd m)) l ->
      Forall (fun k => k <= Z.of_nat M) (txo p d i l)).
    { induction l as [|[k u] r IHl]; intros i Hf Hl; [constructor|].
      apply Forall_cons_iff in Hf as [Hu Hr]. apply Forall_cons_iff in Hl as [[Hk Hlu] Hlr].
      cbn [fst snd] in *. cbn [txo].
      apply Forall_app; split;
        [apply le6M; [exact H6|]; destruct (Nat.eqb i 0); [constructor | constructor; [lia | constructor]]|].
      apply Forall_app; split; [apply le6M; [exact H6|]; destruct p; [apply tx_line_le | constructor]|].
      apply Forall_app; split; [apply le6M; [exact H6 | apply tx_str_le]|].
      apply Forall_app; split; [constructor; [lia | constructor]|].
      apply Forall_app; split; [destruct p; [constructor; [lia | constructor] | constructor]|].
      apply Forall_app; split; [apply Hu; assumption|]. apply IHl; assumption. }
    apply Forall_app; split; [apply Hgo; assumption|].
    apply Forall_app; split;
      [apply le6M; [exact H6|]; destruct ms; [constructor | destruct p; [apply tx_line_le | constructor]]|].
    constructor; [lia | constructor].
Qed.

Theorem rmaxpiece_le : forall sm x t p, json_read sm x = Some t -> rmaxpiece t p <= Z.max 6 (Z.of_nat (length x)).
Proof.
  intros sm x t p H. pose proof (G12_read_len sm x t H) as Ht.
  set (M := Nat.max 6 (length x)).
  assert (H6 : (6 <= M)%nat) by (unfold M; apply Nat.le_max_l).
  assert (HM : tlen M t) by (apply (tlen_mono t (length x)); [unfold M; apply Nat.le_max_r | exact Ht]).
  assert (EM : Z.of_nat M = Z.max 6 (Z.of_nat (length x))) by (unfold M; rewrite Nat2Z.inj_max; reflexivity).
  rewrite <- EM. unfold rmaxpiece, rpieces. apply fmax_le; [lia|].
  apply Forall_app. split; [apply txv_le; assumption|].
  destruct p; [constructor; [lia | constructor] | constructor].
Qed.

(* ================================================================ the parse's class-17 frees *)

Definition in17 (q : Z) : bool := (449 <=? q) && (q <=? 640).

(* containers with at least 9 items; objects with at least 65 members *)
Fixpoint nc9 (t : jv) : nat :=
  match t with
  | JArr items => ((if Nat.leb 9 (length items) then 1 else 0) + list_sum (map nc9 items))%nat
  | JObj ms => ((if Nat.leb 9 (length ms) then 1 else 0) + list_sum (map (fun '(_, u) => nc9 u) ms))%nat
  | _ => 0%nat
  end.

Fixpoint nk65 (t : jv) : nat :=
  match t with
  | JArr items => list_sum (map nk65 items)
  | JObj ms => ((if Nat.leb 65 (length ms) then 1 else 0) + list_sum (map (fun '(_, u) => nk65 u) ms))%nat
  | _ => 0%nat
  end.

Lemma kids17 : forall cap j, Z.of_nat cap = 8 * 2 ^ Z.of_nat j ->
  in17 (Z.of_nat (56 * cap) + HEAD) = true -> cap = 8%nat.
Proof.
  intros cap j Ej H. unfold in17, HEAD in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct j as [|j].
  - change (2 ^ Z.of_nat 0) with 1 in Ej. lia.
  - assert (Hp : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Ej by lia. set (P := 2 ^ Z.of_nat j) in *. lia.
Qed.

Lemma keys17 : forall cap j, Z.of_nat cap = 8 * 2 ^ Z.of_nat j ->
  in17 (Z.of_nat (8 * cap) + HEAD) = true -> cap = 64%nat.
Proof.
  intros cap j Ej H. unfold in17, HEAD in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct j as [|[|[|[|j]]]].
  - change (2 ^ Z.of_nat 0) with 1 in Ej. lia.
  - change (2 ^ Z.of_nat 1) with 2 in Ej. lia.
  - change (2 ^ Z.of_nat 2) with 4 in Ej. lia.
  - change (2 ^ Z.of_nat 3) with 8 in Ej. lia.
  - assert (Hp : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
    rewrite !Nat2Z.inj_succ, !Z.pow_succ_r in Ej by lia. set (P := 2 ^ Z.of_nat j) in *. lia.
Qed.

Lemma hfrees_rd_app : forall a b, hfrees (rd_hevs (a ++ b)) = hfrees (rd_hevs a) ++ hfrees (rd_hevs b).
Proof. intros a b. rewrite rd_hevs_app. apply hfrees_app. Qed.

Lemma hfrees_alloc : forall a, hfrees (rd_hev (EAlloc a)) = [].
Proof. reflexivity. Qed.

Lemma hf_g1 : forall a b, (0 < a)%nat -> hfrees (rd_hevs [EGrow a b]) = [Z.of_nat a + HEAD].
Proof.
  intros a b H. change (rd_hevs [EGrow a b]) with (rd_hev (EGrow a b) ++ []).
  rewrite app_nil_r, (rd_hev_grow_S a b H). reflexivity.
Qed.

Lemma hf_g2 : forall a b c d, (0 < a)%nat -> (0 < c)%nat ->
  hfrees (rd_hevs [EGrow a b; EGrow c d]) = [Z.of_nat a + HEAD; Z.of_nat c + HEAD].
Proof.
  intros a b c d Ha Hc. change (rd_hevs [EGrow a b; EGrow c d]) with (rd_hev (EGrow a b) ++ rd_hev (EGrow c d) ++ []).
  rewrite app_nil_r, (rd_hev_grow_S a b Ha), (rd_hev_grow_S c d Hc). reflexivity.
Qed.

Lemma cnt_one : forall f a, cnt f [a] = (if f a then 1 else 0)%nat.
Proof. intros f a. unfold cnt. cbn [filter]. destruct (f a); reflexivity. Qed.

Lemma cnt_two : forall f a b, cnt f [a; b] = ((if f a then 1 else 0) + (if f b then 1 else 0))%nat.
Proof. intros f a b. unfold cnt. cbn [filter]. destruct (f a), (f b); reflexivity. Qed.

(* a grow at (n, cap) frees a class-17 kids array only at n = 8, a class-17 keys array only at n = 64 *)
Lemma c17_grow : forall o n cap, capok n cap ->
  (cnt in17 (hfrees (rd_hevs (grow_ev o n cap))) <=
   (if Nat.eqb n 8 then 1 else 0) + (if o && Nat.eqb n 64 then 1 else 0))%nat.
Proof.
  intros o n cap Hc. unfold grow_ev. destruct (Nat.ltb n cap) eqn:El.
  { cbn. lia. }
  apply Nat.ltb_ge in El.
  destruct Hc as [[-> ->] | (j & Ej & Hn)].
  { destruct o; cbn; lia. }
  assert (n = cap) by lia. subst n.
  assert (Hp : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hc8 : (8 <= cap)%nat) by (set (P := 2 ^ Z.of_nat j) in *; lia).
  assert (A : ((if in17 (Z.of_nat (56 * cap) + HEAD) then 1 else 0) <= (if Nat.eqb cap 8 then 1 else 0))%nat).
  { destruct (in17 (Z.of_nat (56 * cap) + HEAD)) eqn:E; [|lia]. rewrite (kids17 cap j Ej E). cbn. lia. }
  destruct o; cbv beta iota; cbn [andb].
  - rewrite hf_g2 by lia. rewrite cnt_two.
    assert (B : ((if in17 (Z.of_nat (8 * cap) + HEAD) then 1 else 0) <= (if Nat.eqb cap 64 then 1 else 0))%nat).
    { destruct (in17 (Z.of_nat (8 * cap) + HEAD)) eqn:E; [|lia]. rewrite (keys17 cap j Ej E). cbn. lia. }
    lia.
  - rewrite hf_g1 by lia. rewrite cnt_one. lia.
Qed.

(* the n-th item (from 0) of a container with n + L items at most crosses 8 once, 64 once *)
Definition g9 (n L : nat) : nat := if (Nat.leb n 8 && Nat.leb 9 (n + L)%nat)%bool then 1%nat else 0%nat.
Definition g65 (n L : nat) : nat := if (Nat.leb n 64 && Nat.leb 65 (n + L)%nat)%bool then 1%nat else 0%nat.

Lemma g9_step : forall n L, ((if Nat.eqb n 8 then 1 else 0) + g9 (S n) L <= g9 n (S L))%nat.
Proof.
  intros n L. unfold g9.
  destruct (Nat.eqb_spec n 8); destruct (Nat.leb_spec0 (S n) 8); destruct (Nat.leb_spec0 9 (S n + L));
    destruct (Nat.leb_spec0 n 8); destruct (Nat.leb_spec0 9 (n + S L)); cbn [andb]; lia.
Qed.

Lemma g65_step : forall n L, ((if Nat.eqb n 64 then 1 else 0) + g65 (S n) L <= g65 n (S L))%nat.
Proof.
  intros n L. unfold g65.
  destruct (Nat.eqb_spec n 64); destruct (Nat.leb_spec0 (S n) 64); destruct (Nat.leb_spec0 65 (S n + L));
    destruct (Nat.leb_spec0 n 64); destruct (Nat.leb_spec0 65 (n + S L)); cbn [andb]; lia.
Qed.

Lemma c17_tgo_arr : forall l n cap, capok n cap ->
  (cnt in17 (hfrees (rd_hevs (tgo_arr n cap l))) <=
   g9 n (length l) + list_sum (map (fun u => cnt in17 (hfrees (rd_hevs (ttrace u)))) l))%nat.
Proof.
  induction l as [|u r IH]; intros n cap Hc.
  - cbn. lia.
  - cbn [tgo_arr length map]. rewrite lsum_cons, !hfrees_rd_app, !cnt_app.
    pose proof (c17_grow false n cap Hc) as G. cbn [andb] in G.
    pose proof (IH (S n) (gcap n cap) (capok_step n cap Hc)) as I.
    pose proof (g9_step n (length r)). lia.
Qed.

Lemma c17_tgo_obj : forall l n cap, capok n cap ->
  (cnt in17 (hfrees (rd_hevs (tgo_obj n cap l))) <=
   g9 n (length l) + g65 n (length l) +
   list_sum (map (fun m => cnt in17 (hfrees (rd_hevs (ttrace (snd m))))) l))%nat.
Proof.
  induction l as [|[k u] r IH]; intros n cap Hc.
  - cbn. lia.
  - cbn [tgo_obj length map snd]. rewrite lsum_cons, hfrees_rd_app, rd_hevs_cons, hfrees_app, hfrees_alloc,
      app_nil_l, hfrees_rd_app, !cnt_app.
    pose proof (c17_grow true n cap Hc) as G. cbn [andb] in G.
    pose proof (IH (S n) (gcap n cap) (capok_step n cap Hc)) as I.
    pose proof (g9_step n (length r)). pose proof (g65_step n (length r)). lia.
Qed.

Lemma lsum_le3 : forall (A : Type) (f g h : A -> nat) (l : list A), Forall (fun a => (f a <= g a + h a)%nat) l ->
  (list_sum (map f l) <= list_sum (map g l) + list_sum (map h l))%nat.
Proof. intros A f g h l H. induction H as [|a l Ha _ IH]; [cbn; lia|]. cbn [map]. rewrite !lsum_cons. lia. Qed.

Lemma c17_tt : forall t, (cnt in17 (hfrees (rd_hevs (ttrace t))) <= nc9 t + nk65 t)%nat.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - rewrite tt_arr. eapply Nat.le_trans; [apply c17_tgo_arr; left; split; reflexivity|].
    cbn [nc9 nk65].
    pose proof (lsum_le3 _ (fun u => cnt in17 (hfrees (rd_hevs (ttrace u)))) nc9 nk65 items IH) as S3.
    assert (E : g9 0 (length items) = if Nat.leb 9 (length items) then 1%nat else 0%nat) by reflexivity.
    rewrite E. lia.
  - rewrite tt_obj. eapply Nat.le_trans; [apply c17_tgo_obj; left; split; reflexivity|].
    cbn [nc9 nk65].
    assert (H : Forall (fun m => (cnt in17 (hfrees (rd_hevs (ttrace (snd m)))) <=
                  (fun '(_, u) => nc9 u) m + (fun '(_, u) => nk65 u) m)%nat) ms).
    { eapply Forall_impl; [|exact IH]. intros [k u] Hu. exact Hu. }
    pose proof (lsum_le3 _ (fun m => cnt in17 (hfrees (rd_hevs (ttrace (snd m)))))
      (fun '(_, u) => nc9 u) (fun '(_, u) => nk65 u) ms H) as S3.
    assert (E1 : g9 0 (length ms) = if Nat.leb 9 (length ms) then 1%nat else 0%nat) by reflexivity.
    assert (E2 : g65 0 (length ms) = if Nat.leb 65 (length ms) then 1%nat else 0%nat) by reflexivity.
    rewrite E1, E2. lia.
Qed.

Theorem parse_frees17 : forall sm t p, pj_wf sm t ->
  (length (filter (fun q => ((449 <=? q) && (q <=? 640))%Z) (hfrees (parse_evs sm (wdoc t p) []))) <=
   nc9 t + nk65 t)%nat.
Proof. intros sm t p Hw. rewrite (parse_wf sm t p Hw). exact (c17_tt t). Qed.
