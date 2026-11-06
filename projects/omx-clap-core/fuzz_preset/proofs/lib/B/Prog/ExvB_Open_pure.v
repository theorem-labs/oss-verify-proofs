(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CI (container open, B entry + 0x374): the PURE
   facts the segment needs, over ExvB_Stmt.v's model names (exv_V = prhex_V dep (exv_X E); exv_L = the plain ex_L
   shape over PjGrammar.jrl). The grammar's jr_cont (PjGrammar.v:254-263) is what the code does at '{' / '[': the depth
   check (MAXD < S d refuses), skip (tl x), the closer test, else the items loop at S d from the empty list. Plain
   ex_value_m.v's ex_V unfolding is restated here over PjGrammar's own fuel lemma (fuel_mono, PjGrammar.v:1248); no
   plain lemma is cited.
   - exv_skip_skipn / exv_ip_skip: skip of a suffix of the text is the suffix at len - length (skip ..): the cursor
     position the code holds after ex_ws.
   - exv_skipX: skip (exv_X E) = c :: skipn (i1 + 1) x at the opening byte c.
   - exv_V_deep / exv_V_close / exv_V_loop: the three arms of jr_cont.
   - exv_dif_v0 / exv_dif_mis / exv_dif_match: the differs bookkeeping at acc = [] for the three type-check arms.
   Rule 24: proves no function (kind: segment lemma helper). Numerals: 32 (WORD: MAXD, PjGrammar.v:6), 91 / 93 / 123 /
   125 (WORD: '[' ']' '{' '}'), 5 / 6 (WORD: PjTree.tag of an array / object), 2 (LENGTH: grammar fuel factor). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Open Scope Z_scope.

Lemma exv_skipn_len : forall (x : list Z) m, skipn m x = skipn (length x - length (skipn m x)) x.
Proof.
intros x m. destruct (Nat.le_gt_cases m (length x)) as [H|H].
- rewrite length_skipn. replace (length x - (length x - m))%nat with m by lia. reflexivity.
- rewrite (skipn_all2 x) by lia. cbn [length]. rewrite Nat.sub_0_r, skipn_all. reflexivity.
Qed.

Lemma exv_skip_suffix : forall l, exists j, PjGrammar.skip l = skipn j l.
Proof.
induction l as [|b r IH]; [exists 0%nat; reflexivity|].
cbn [PjGrammar.skip]. destruct (PjGrammar.ws b).
- destruct IH as [j Hj]. exists (S j). exact Hj.
- exists 0%nat. reflexivity.
Qed.

Lemma exv_skip_skipn : forall (x : list Z) k,
  PjGrammar.skip (skipn k x) = skipn (length x - length (PjGrammar.skip (skipn k x))) x.
Proof.
intros x k. destruct (exv_skip_suffix (skipn k x)) as [j Hj]. rewrite Hj, skipn_skipn. apply exv_skipn_len.
Qed.

(* the cursor position after ex_ws, as a text index *)
Lemma exv_ip_skip : forall (x : list Z) k,
  let ip := Z.of_nat (length x) - Z.of_nat (length (PjGrammar.skip (skipn k x))) in
  skipn (Z.to_nat ip) x = PjGrammar.skip (skipn k x) /\ 0 <= ip <= Z.of_nat (length x).
Proof.
intros x k ip.
pose proof (PjGrammar.skip_len (skipn k x)) as H1. pose proof (PjGrammar.skipn_len_le k x) as H2.
split; [|unfold ip; lia].
unfold ip. rewrite <- Nat2Z.inj_sub by lia. rewrite Nat2Z.id. symmetry. apply exv_skip_skipn.
Qed.

Lemma exv_skipn_nth : forall (x : list Z) k, (k < length x)%nat -> skipn k x = nth k x 0 :: skipn (S k) x.
Proof.
induction x as [|b r IH]; intros [|k] Hk; cbn [length] in Hk; try lia; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.

(* the value's first byte after the whitespace is the opening byte c at i1 *)
Lemma exv_skipX : forall E c,
  0 <= e_i0 E <= exv_len E -> exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c ->
  PjGrammar.skip (exv_X E) = c :: skipn (S (Z.to_nat (exv_i1 E))) (e_x E).
Proof.
intros E c Hi0 Hi1 Hc. unfold exv_i1, exv_len, exv_X in *.
destruct (exv_ip_skip (e_x E) (Z.to_nat (e_i0 E))) as [Hs Hb]. cbv zeta in Hs, Hb.
assert (Hk : (Z.to_nat (Z.of_nat (length (e_x E)) - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (e_i0 E)) (e_x E)))))
  < length (e_x E))%nat) by lia.
revert Hs Hc Hk.
generalize (Z.to_nat (Z.of_nat (length (e_x E)) - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (e_i0 E)) (e_x E)))))).
intros k Hs Hc Hk. rewrite <- Hs. rewrite (exv_skipn_nth (e_x E) k Hk), Hc. reflexivity.
Qed.

Section v.
Variable E : exv_e.
Variable c : Z.
Variable y : list Z.
Hypothesis HX : PjGrammar.skip (exv_X E) = c :: y.
Hypothesis Hc : c = 91 \/ c = 123.
Let o := (c =? 123).

Lemma exv_V_cont : exv_V E = exv_run0
  (PjGrammar.jr_cont (PjGrammar.jrl ReaderRes.jr_strtod (2 * length (exv_X E))%nat) (Z.to_nat (e_dep E)) o (c :: y)).
Proof.
unfold exv_V, prhex_V, exv_run0, PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite HX.
unfold o. destruct Hc as [-> | ->]; reflexivity.
Qed.

Lemma exv_lenX : (S (length y) <= length (exv_X E))%nat.
Proof. pose proof (PjGrammar.skip_len (exv_X E)) as H. rewrite HX in H. cbn [length] in H. exact H. Qed.

(* depth 32: MAXD < S 32, the grammar refuses *)
Lemma exv_V_deep : e_dep E = 32 -> exv_V E = None.
Proof. intros Hd. rewrite exv_V_cont, Hd. reflexivity. Qed.

(* the closer right after the whitespace: the empty container *)
Lemma exv_V_close : forall c' r, 0 <= e_dep E -> e_dep E + 1 <= 32 ->
  PjGrammar.skip y = c' :: r -> c' = PjGrammar.closer o ->
  exv_V E = Some (PjGrammar.mk o (rev []), r).
Proof.
intros c' r H0 H1 Hy Hc'. rewrite exv_V_cont. unfold exv_run0, PjGrammar.jr_cont.
replace (Nat.ltb PjGrammar.MAXD (S (Z.to_nat (e_dep E)))) with false
  by (symmetry; apply Nat.ltb_ge; unfold PjGrammar.MAXD; lia).
cbn [tl]. rewrite Hy. rewrite Hc', Z.eqb_refl. reflexivity.
Qed.

(* otherwise the items loop at S d from the empty list, at the cursor skip y *)
Lemma exv_V_loop : 0 <= e_dep E -> e_dep E + 1 <= 32 ->
  (forall c' r, PjGrammar.skip y = c' :: r -> c' <> PjGrammar.closer o) ->
  exv_V E = exv_L (S (Z.to_nat (e_dep E))) o 0 0 [] (PjGrammar.skip y).
Proof.
intros H0 H1 Hn. rewrite exv_V_cont. unfold exv_L, exv_run0, PjGrammar.jr_cont.
replace (Nat.ltb PjGrammar.MAXD (S (Z.to_nat (e_dep E)))) with false
  by (symmetry; apply Nat.ltb_ge; unfold PjGrammar.MAXD; lia).
cbn [tl]. pose proof exv_lenX as HL. pose proof (PjGrammar.skip_len y) as Hy.
destruct (PjGrammar.skip y) as [|c' r] eqn:Ey.
- rewrite (proj2 (PjGrammar.fuel_mono ReaderRes.jr_strtod (2 * length (@nil Z) + 2)%nat) _ _ _ _ _ _ (2 * length (exv_X E))%nat) by (cbn [length]; lia).
  reflexivity.
- replace (c' =? PjGrammar.closer o) with false by (symmetry; apply Z.eqb_neq; exact (Hn c' r eq_refl)).
  rewrite (proj2 (PjGrammar.fuel_mono ReaderRes.jr_strtod (2 * length (c' :: r) + 2)%nat) _ _ _ _ _ _ (2 * length (exv_X E))%nat) by lia.
  reflexivity.
Qed.
End v.

(* the differs bookkeeping at acc = [] *)
Lemma exv_dif_v0 : forall E o, e_v E = 0 -> exv_dif E o 0 (e_dl E) [].
Proof. intros E o Hv. left. split; [reflexivity|]. split; [intros _; reflexivity | intros H; exfalso; exact (H Hv)]. Qed.

Lemma exv_dif_mis : forall E (o : bool), e_v E <> 0 -> PjTree.tag (e_t E) <> (if o then 6 else 5) -> exv_dif E o 0 1 [].
Proof.
intros E o Hv Ht. left. split; [reflexivity|]. split; [intros H; exfalso; exact (Hv H) | intros _; split; [reflexivity | exact Ht]].
Qed.

Lemma exv_dif_match : forall E (o : bool), e_v E <> 0 -> PjTree.tag (e_t E) = (if o then 6 else 5) ->
  exv_dif E o (e_v E) (e_dl E) [].
Proof.
intros E o Hv Ht. right. split; [reflexivity|]. split; [exact Hv|]. split; [exact Ht|].
assert (HP : exv_pref o [] (e_t E)).
{ destruct o, (e_t E); cbn [PjTree.tag] in Ht; try discriminate; cbn [exv_pref length firstn rev]; split; auto; lia. }
split; [intros H; left; exact H | intros [H|H]; [exact H | exfalso; exact (H HP)]].
Qed.
