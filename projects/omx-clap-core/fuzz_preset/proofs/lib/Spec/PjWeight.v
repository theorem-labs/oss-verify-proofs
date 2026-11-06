(* A weighted count of a JSON tree's nodes, bounded jointly by the input length and the pretty length.

   For a tree t read from input x, wsum W t adds up the weights of t's nodes:
     - a container's own weight: w_c18 for 1 <= n <= 8 items, w_c9 for n >= 9 items;
     - w_k64 ON TOP of that for an object with >= 33 members (such an object has >= 9 members, so it
       pays w_c9 as well); it covers both a 33..64-member object (its keys array is the 528-byte,
       768-class one) and a >= 65-member object (its 64-slot keys array is freed into that class);
     - w_str for a string value or a member name of decoded length >= 72, w_num for a number whose text
       is >= 432 bytes;
     - w_len per byte of a string's / name's decoded length and of a number's text length, but only for
       a piece of length >= w_lmin (only a piece at least as long as the writer's capacity can make its
       chain skip a doubling; a short piece pays nothing).

   wt_read / wt_read_obj bound wsum W t by b * |x| + c * (the pretty length of t) + an allowance, as ONE
   weighted induction over the parse with a per-depth allowance al, in the shape of SlotSizes' Section W
   (w_fuel / w_read): the per-depth numeric facts HL / HA / HO / HIa / HIo are hypotheses, and each
   instance discharges them from a finite table with vm_compute.

   wt_live bounds the trees live at RT3 together, the doc read p times and its copy 3 - p times
   (PresetReqAt.copy_set: one root member set in place or appended), against the copy's pretty length:
   wt_rt3_live is p = 1 (the doc and two copies), wt_rt3_live2 is p = 2 (the doc twice, as D3 counts it,
   and one copy). It reuses the machine's item loop per member (JL), so the copies need not spend the
   replaced value's input bytes, and SlotSizes' pretty rate (56 bytes per input byte) bounds that
   value's own pretty text. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
WriterSpec WriterValue PjWriteHyp SlotSizes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
Import ListNotations.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* the weights of a tree's nodes                                       *)
(* ------------------------------------------------------------------ *)

Record nweights := {
  w_c18 : Z;      (* a container with 1 <= n <= 8 items (its kids array is the 464-byte, 768-class one) *)
  w_c9  : Z;      (* a container with n >= 9 items *)
  w_k64 : Z;      (* an object with n >= 33 members, ON TOP OF w_c9 *)
  w_str : Z;      (* a string value or member name of decoded length >= 72 *)
  w_num : Z;      (* a number whose text has length >= 432 *)
  w_len : Z;      (* per byte of a piece of length >= w_lmin *)
  w_lmin : nat    (* the length from which a piece pays w_len per byte *)
}.

Definition cwt (W : nweights) (n : nat) : Z :=
  if Nat.eqb n 0 then 0 else if Nat.leb n 8 then w_c18 W else w_c9 W.

Definition kwt (W : nweights) (n : nat) : Z :=
  if Nat.leb 33 n then w_k64 W else 0.

Definition swt (W : nweights) (k : nat) : Z :=
  (if Nat.leb 72 k then w_str W else 0) +
  (if Nat.leb (w_lmin W) k then w_len W * Z.of_nat k else 0).

Definition nwt (W : nweights) (k : nat) : Z :=
  (if Nat.leb 432 k then w_num W else 0) +
  (if Nat.leb (w_lmin W) k then w_len W * Z.of_nat k else 0).

Fixpoint wsum (W : nweights) (t : jv) : Z :=
  match t with
  | JNull => 0
  | JFalse => 0
  | JTrue => 0
  | JNum txt _ => nwt W (length txt)
  | JStr s => swt W (length s)
  | JArr items => cwt W (length items) + fold_right Z.add 0 (map (wsum W) items)
  | JObj ms => cwt W (length ms) + kwt W (length ms) +
      fold_right Z.add 0 (map (fun m => swt W (length (fst m)) + wsum W (snd m)) ms)
  end.

(* the weight of a container's item list, as the reader builds it *)
Definition mw (W : nweights) (o : bool) (m : list Z * jv) : Z :=
  (if o then swt W (length (fst m)) else 0) + wsum W (snd m).

Definition wl (W : nweights) (o : bool) (l : list (list Z * jv)) : Z :=
  fold_right Z.add 0 (map (mw W o) l).

Lemma fr_map_ext : forall (A : Type) (f g : A -> Z) (l : list A),
  (forall a, f a = g a) -> fold_right Z.add 0 (map f l) = fold_right Z.add 0 (map g l).
Proof.
  intros A f g l H. induction l as [|a l IH]; [reflexivity|].
  cbn [map fold_right]. rewrite H, IH. reflexivity.
Qed.

Lemma wsum_mk : forall W o l,
  wsum W (mk o l) = cwt W (length l) + (if o then kwt W (length l) else 0) + wl W o l.
Proof.
  intros W o l. unfold mk. destruct o; cbv beta iota.
  - cbn [wsum]. unfold wl, mw. cbn [fst snd]. reflexivity.
  - cbn [wsum]. rewrite length_map, map_map. unfold wl.
    assert (Hx : forall m : list Z * jv, wsum W (snd m) = mw W false m)
      by (intros m; unfold mw; cbv beta iota; lia).
    rewrite (fr_map_ext _ _ _ l Hx). lia.
Qed.

Lemma wl_cons : forall W o m l, wl W o (m :: l) = mw W o m + wl W o l.
Proof. intros W o m l. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* escapes: a decoded byte is at least one byte of the written text    *)
(* ------------------------------------------------------------------ *)

Lemma ech_ge : forall ch, (1 <= length (ech ch))%nat.
Proof.
  intros ch. unfold ech, esc. destruct (special ch); [|cbn [length]; lia].
  destruct (ch =? 34); [cbn [length]; lia|]. destruct (ch =? 92); [cbn [length]; lia|].
  destruct (ch =? 10); [cbn [length]; lia|]. destruct (ch =? 9); [cbn [length]; lia|].
  destruct (ch =? 13); cbn [length]; lia.
Qed.

Lemma fme_ge : forall l, (length l <= length (flat_map ech l))%nat.
Proof.
  induction l as [|ch l IH]; [cbn [length]; lia|].
  cbn [flat_map length]. rewrite length_app. pose proof (ech_ge ch). lia.
Qed.

(* a decoded string, its remainder and the closing quote all fit in the input *)
Lemma dec_k : forall x s r, decode x = Some (s, r) -> (length s + length r + 1 <= length x)%nat.
Proof.
  intros x s r H. destruct (decode_stop x s r H) as (q & Hs & -> & Hl & _ & _).
  destruct (scan_quote x q Hs) as [Hq _]. rewrite length_skipn. lia.
Qed.

(* a member's name: its decoded bytes, the two quotes and the colon all fit in the input *)
Lemma name_k : forall o y ok nm y1 tn ok', jr_name o y ok = (Some (nm, y1), tn, ok') ->
  if o then (length nm + 3 + length y1 <= length y)%nat else y1 = y.
Proof.
  intros o y ok nm y1 tn ok' H. unfold jr_name in H. destruct o; cbv beta iota in H |- *.
  - destruct (skip y) as [|bb z] eqn:Ey; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
    pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
    destruct (bb =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([nm0 r] & t1 & ok1 & t2 & Hs & H & _).
    pose proof (jr_string_spec z ok) as Hsp. rewrite Hs in Hsp. destruct Hsp as (q & _ & Hd & _ & Hl).
    pose proof (dec_k z nm0 r Hd) as D.
    cbv beta iota in H.
    destruct (skip r) as [|ch r1] eqn:Er; cbv beta iota in H.
    + unfold jbind, jfree, jrefuse in H. cbv beta iota in H. discriminate H.
    + pose proof (skip_len r) as Hr. rewrite Er in Hr. cbn [length] in Hr.
      destruct (ch =? 58); cbv beta iota in H.
      * unfold jret in H. injection H as E1 E2 _ _. subst nm0 r1. lia.
      * unfold jbind, jfree, jrefuse in H. cbv beta iota in H. discriminate H.
  - unfold jret in H. injection H as _ E _ _. symmetry. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* the copy RT3 reads back: a member set in place, or appended          *)
(* ------------------------------------------------------------------ *)

(* a copy's member: the doc's member, or the doc's member with its value replaced by tv *)
Definition mrel (tv : jv) (m m' : list Z * jv) : Prop :=
  fst m' = fst m /\ (snd m' = snd m \/ snd m' = tv).

Lemma mrel_refl : forall tv l, Forall2 (mrel tv) l l.
Proof.
  intros tv l. induction l as [|m l IH]; constructor; [split; [reflexivity | left; reflexivity] | exact IH].
Qed.

(* pj_set_model appends the member, or replaces the value of one member *)
Lemma set_cases : forall ms k tv,
  pj_set_model ms k tv = ms ++ [(k, tv)] \/ Forall2 (mrel tv) ms (pj_set_model ms k tv).
Proof.
  induction ms as [|[k0 v0] r IH]; intros k tv; cbn [pj_set_model].
  - left. reflexivity.
  - destruct (list_eq_dec Z.eq_dec k0 k) as [E|E].
    + right. constructor; [split; [reflexivity | right; reflexivity] | apply mrel_refl].
    + destruct (IH k tv) as [H|H].
      * left. rewrite H. reflexivity.
      * right. constructor; [split; [reflexivity | left; reflexivity] | exact H].
Qed.

Lemma wl_app1 : forall W o l m, wl W o (l ++ [m]) = wl W o l + mw W o m.
Proof.
  intros W o l m. induction l as [|m0 l IH]; cbn [app].
  - unfold wl. cbn [map fold_right]. lia.
  - rewrite !wl_cons, IH. lia.
Qed.

Lemma wgo_app1 : forall o d l n m,
  Z.of_nat (length (concat (wgo true o d n (l ++ [m])))) =
  Z.of_nat (length (concat (wgo true o d n l))) +
  (if Nat.eqb (n + length l) 0 then 0 else 1) + indl true (S d) + NP true o (fst m) + Wv true (S d) (snd m).
Proof.
  intros o d l. induction l as [|[k u] l IH]; intros n [k' u'].
  - cbn [app length]. rewrite Nat.add_0_r. rewrite wgo_cons, !wgo_nil. cbn [fst snd].
    destruct (Nat.eqb n 0); lia.
  - cbn [app length]. rewrite !wgo_cons, (IH (S n) (k', u')).
    rewrite Nat.add_succ_r. cbn [Nat.eqb Nat.add]. cbv beta iota.
    destruct (Nat.eqb n 0); lia.
Qed.

(* SlotSizes' pretty rate: a value's pretty text at depth d is at most 56 bytes per input byte *)
Lemma wv_rate : forall sm f d x ok v r tr ok', jrv sm f d x ok = (Some (v, r), tr, ok') ->
  Wv true d v + 56 * Z.of_nat (length r) <= 56 * Z.of_nat (length x) + G d.
Proof.
  intros sm f d x ok v r tr ok' H.
  refine (proj2 (proj1 (w_fuel sm true 56 G _ _ _ _ f) d x ok v r tr ok' H)).
  - lia.
  - intros d'. pose proof (G_lo d'). lia.
  - intros k Hk. destruct (G_step k Hk) as [K1 K2]. unfold indl. cbv beta iota. lia.
  - intros k Hk. destruct (G_step k Hk) as [K1 K2]. unfold indl. cbv beta iota. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the generic bound                                                   *)
(* ------------------------------------------------------------------ *)

Section WT.
Variable sm : list Z -> Z * Z.
Variable W : nweights.
Variables (b c : Z).          (* the weight of an input byte; the weight of a pretty byte *)
Variable al : nat -> Z.       (* the per-depth allowance, as SlotSizes' al *)
Variable alo : nat -> Z.      (* the allowance of an OBJECT root *)

(* the weight a container charges on top of its items *)
Definition wtc : Z := Z.max (w_c18 W) (w_c9 W).

(* the most a member's name can exceed the >= |nm| + 3 input bytes and >= |nm| + 4 pretty bytes it costs:
   a short name, a name of 72 bytes below the w_len threshold, a name at the threshold *)
Definition wtk : Z :=
  Z.max (-3 * b - 4 * c)
 (Z.max (w_str W - 72 * (b + c) - 3 * b - 4 * c)
        (w_str W + Z.of_nat (w_lmin W) * (w_len W - b - c) - 3 * b - 4 * c)).

(* the most a leaf (literal, number, string) or an empty container can exceed what it costs:
   two brackets / quotes, one digit, a 72-byte string, a 432-byte number, and a piece at the threshold *)
Definition wtl : Z :=
  Z.max (-2 * b - 2 * c)
 (Z.max (- b - c)
 (Z.max (w_str W - 74 * (b + c))
 (Z.max (w_num W - 432 * (b + c))
 (Z.max (w_str W + Z.of_nat (w_lmin W) * (w_len W - b - c) - 2 * b - 2 * c)
        (w_num W + Z.of_nat (w_lmin W) * (w_len W - b - c)))))).

(* what a non-empty container at depth d of kind o may exceed its input and pretty text by: its own
   weight and its first item's allowance, less its two brackets, its first item's line and its closing
   line *)
Definition wfirst (d : nat) (o : bool) : Z :=
  wtc + (if o then wtk else 0) - 2 * b - c * (4 * Z.of_nat d + 6) + al (S d).

(* what an item after the first leaves over, once it has paid its comma, its line and (for an object) its
   name and its share of w_k64; it must not be positive, else a container could repeat it without end *)
Definition wlater (d : nat) (o : bool) : Z :=
  al (S d) + (if o then wtk + w_k64 W else 0) - b - c * (2 * Z.of_nat d + 4).

Definition wcb (d : nat) (o : bool) : Z := Z.max (-2 * b - 2 * c) (wfirst d o).

Hypothesis Hb : 0 <= b.
Hypothesis Hc : 0 <= c.
Hypothesis Hk : 0 <= w_k64 W.
Hypothesis Hwl : w_len W <= b.                      (* the input pays each byte of a long piece *)
Hypothesis HT : (432 <= w_lmin W)%nat.              (* the threshold is above the w_str / w_num ones *)
Hypothesis HL : forall d, (d <= 32)%nat -> wtl <= al d.
Hypothesis HA : forall d, (d < 32)%nat -> wfirst d false <= al d.
Hypothesis HO : forall d, (d < 32)%nat -> wfirst d true <= al d.
Hypothesis HIa : forall d, (1 <= d)%nat -> (d < 32)%nat -> wlater d false <= 0.
Hypothesis HIo : forall d, (d < 32)%nat -> wlater d true <= 0.

(* ---- small arithmetic ---- *)

Lemma bm : forall n m : nat, (n <= m)%nat -> b * Z.of_nat n <= b * Z.of_nat m.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. intros n m H. apply Z.mul_le_mono_nonneg_l; [exact Hb | lia]. Qed.

Lemma cm : forall x y : Z, x <= y -> c * x <= c * y.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. intros x y H. apply Z.mul_le_mono_nonneg_l; [exact Hc | exact H]. Qed.

Lemma mul_nonpos_mono : forall m p q, m <= 0 -> p <= q -> m * q <= m * p.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. intros m p q H1 H2. nia. Qed.

Lemma bc_nonneg : forall n : nat, 0 <= (b + c) * Z.of_nat n.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. intros n. apply Z.mul_nonneg_nonneg; lia. Qed.

Lemma bc_mono : forall (p : Z) (n : nat), p <= Z.of_nat n -> (b + c) * p <= (b + c) * Z.of_nat n.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. intros p n H. apply Z.mul_le_mono_nonneg_l; lia. Qed.

Lemma wmc : w_len W - b - c <= 0.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. lia. Qed.

Lemma wtl_lb : -2 * b - 2 * c <= wtl.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. unfold wtl. lia. Qed.

Lemma cwt_le : forall n, (1 <= n)%nat -> cwt W n <= wtc.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros n Hn. unfold cwt, wtc.
  destruct (Nat.eqb n 0) eqn:E; [apply Nat.eqb_eq in E; lia|].
  destruct (Nat.leb n 8); [apply Z.le_max_l | apply Z.le_max_r].
Qed.

Lemma kwt_le : forall n, (1 <= n)%nat -> kwt W n <= w_k64 W * (Z.of_nat n - 1).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros n Hn. unfold kwt. destruct (Nat.leb 33 n) eqn:E.
  - apply Nat.leb_le in E.
    assert (K : 0 <= w_k64 W * (Z.of_nat n - 2)) by (apply Z.mul_nonneg_nonneg; lia).
    replace (Z.of_nat n - 1) with (1 + (Z.of_nat n - 2)) by lia.
    rewrite Z.mul_add_distr_l, Z.mul_1_r. lia.
  - assert (K : 0 <= w_k64 W * (Z.of_nat n - 1)) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

(* ---- the leaves and the names ---- *)

Lemma swt_bnd : forall k, swt W k <= (b + c) * Z.of_nat k + 2 * b + 2 * c + wtl.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros k. unfold swt, wtl. pose proof wmc as M. pose proof HT as H4.
  destruct (Nat.leb (w_lmin W) k) eqn:ET.
  - apply Nat.leb_le in ET.
    rewrite (proj2 (Nat.leb_le 72 k) ltac:(lia)).
    pose proof (mul_nonpos_mono (w_len W - b - c) (Z.of_nat (w_lmin W)) (Z.of_nat k) M
                  ltac:(apply Nat2Z.inj_le; lia)) as P.
    lia.
  - apply Nat.leb_nle in ET. destruct (Nat.leb 72 k) eqn:E72.
    + apply Nat.leb_le in E72.
      pose proof (bc_mono 72 k ltac:(lia)) as Q. lia.
    + pose proof (bc_nonneg k) as Q. lia.
Qed.

Lemma nwt_bnd : forall k, (1 <= k)%nat -> nwt W k <= (b + c) * Z.of_nat k + wtl.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros k Hk1. unfold nwt, wtl. pose proof wmc as M. pose proof HT as H4.
  destruct (Nat.leb (w_lmin W) k) eqn:ET.
  - apply Nat.leb_le in ET.
    rewrite (proj2 (Nat.leb_le 432 k) ltac:(lia)).
    pose proof (mul_nonpos_mono (w_len W - b - c) (Z.of_nat (w_lmin W)) (Z.of_nat k) M
                  ltac:(apply Nat2Z.inj_le; lia)) as P.
    lia.
  - apply Nat.leb_nle in ET. destruct (Nat.leb 432 k) eqn:E432.
    + apply Nat.leb_le in E432. pose proof (bc_mono 432 k ltac:(lia)) as Q. lia.
    + pose proof (bc_mono 1 k ltac:(lia)) as Q. lia.
Qed.

Lemma swt_name : forall k, swt W k <= b * (Z.of_nat k + 3) + c * (Z.of_nat k + 4) + wtk.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros k. unfold swt, wtk. pose proof wmc as M. pose proof HT as H4.
  destruct (Nat.leb (w_lmin W) k) eqn:ET.
  - apply Nat.leb_le in ET.
    rewrite (proj2 (Nat.leb_le 72 k) ltac:(lia)).
    pose proof (mul_nonpos_mono (w_len W - b - c) (Z.of_nat (w_lmin W)) (Z.of_nat k) M
                  ltac:(apply Nat2Z.inj_le; lia)) as P.
    lia.
  - apply Nat.leb_nle in ET. destruct (Nat.leb 72 k) eqn:E72.
    + apply Nat.leb_le in E72. pose proof (bc_mono 72 k ltac:(lia)) as Q. lia.
    + pose proof (bc_nonneg k) as Q. lia.
Qed.

(* ---- the pretty text of the pieces ---- *)

Lemma wv_str : forall d s, Wv true d (JStr s) = Z.of_nat (length (flat_map ech s)) + 2.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros d s. unfold Wv. cbn [wvpieces]. rewrite wstr_eq. cbn [length].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma wv_num : forall d txt bits, Wv true d (JNum txt bits) = Z.of_nat (length txt).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. intros d txt bits. unfold Wv. cbn [wvpieces concat]. rewrite app_nil_r. reflexivity. Qed.

Lemma np_ge : forall nm, Z.of_nat (length nm) + 4 <= NP true true nm.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros nm. unfold NP. cbv beta iota. rewrite wstr_eq. cbn [length]. rewrite length_app.
  cbn [length]. pose proof (fme_ge nm). unfold wsep. cbn [length]. lia.
Qed.

Lemma np_nil : forall nm, NP true false nm = 0.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo. intros nm. reflexivity. Qed.

(* a member's name costs the input at least |nm| + 3 bytes and the pretty text NP bytes *)
Lemma name_bnd : forall o y ok nm y1 tn ok', jr_name o y ok = (Some (nm, y1), tn, ok') ->
  (length y1 <= length y)%nat /\
  (if o then swt W (length nm) else 0) + b * Z.of_nat (length y1) <=
    b * Z.of_nat (length y) + c * NP true o nm + (if o then wtk else 0).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros o y ok nm y1 tn ok' H. pose proof (name_k o y ok nm y1 tn ok' H) as Hn.
  destruct o; cbv beta iota in Hn |- *.
  - split; [lia|].
    pose proof (swt_name (length nm)) as S1.
    pose proof (np_ge nm) as N1. pose proof (cm _ _ N1) as N2.
    pose proof (bm (length nm + 3 + length y1) (length y) Hn) as B1.
    lia.
  - subst y1. split; [lia|].
    rewrite np_nil. lia.
Qed.

(* ---- the invariant of one parsed value ---- *)

Definition wbnd (d : nat) (v : jv) (nr nx : nat) : Prop :=
  match v with
  | JArr _ => (d < 32)%nat /\
      wsum W v + b * Z.of_nat nr <= b * Z.of_nat nx + c * Wv true d v + wcb d false
  | JObj _ => (d < 32)%nat /\
      wsum W v + b * Z.of_nat nr <= b * Z.of_nat nx + c * Wv true d v + wcb d true
  | _ => wsum W v + b * Z.of_nat nr <= b * Z.of_nat nx + c * Wv true d v + wtl
  end.

(* the same, but an array's / object's bound is owed only once its kind's "later item" fact is given:
   an object root needs no fact about an array root's later items, and instance 1 has none *)
Definition wbnd' (d : nat) (v : jv) (nr nx : nat) : Prop :=
  match v with
  | JArr _ => ((d < 32)%nat -> wlater d false <= 0) -> wbnd d v nr nx
  | JObj _ => ((d < 32)%nat -> wlater d true <= 0) -> wbnd d v nr nx
  | _ => wbnd d v nr nx
  end.

(* the share of w_k64 the items n .. n + k - 1 of a container carry: one per item after the first *)
Definition wkch (o : bool) (n k : nat) : Z :=
  if o then w_k64 W * (Z.of_nat k - (if Nat.eqb n 0 then 1 else 0)) else 0.

(* what the loop over the items n .. may exceed its input and its own pretty text by: at n = 0 the first
   item's allowance, its line and the byte that ends it; after that nothing *)
Definition Bw (d : nat) (o : bool) (n : nat) : Z :=
  if Nat.eqb n 0 then al (S d) + (if o then wtk else 0) - b - c * (2 * Z.of_nat d + 3) else 0.

Definition KRL (f : nat) : Prop := forall d o n cap acc y ok v r tr ok', (d < 32)%nat ->
  jrl sm f (S d) o n cap acc y ok = (Some (v, r), tr, ok') ->
  exists nw, nw <> [] /\ v = mk o (rev acc ++ nw) /\ (length r < length y)%nat /\
    (wlater d o <= 0 ->
     wl W o nw + wkch o n (length nw) + b * Z.of_nat (length r) <=
       b * Z.of_nat (length y) + c * Z.of_nat (length (concat (wgo true o d n nw))) + Bw d o n).

(* ---- a container ---- *)

Lemma cont_k : forall f d o bb y ok v r tr ok', KRL f ->
  jr_cont (jrl sm f) d o (bb :: y) ok = (Some (v, r), tr, ok') ->
  (length r < length (bb :: y))%nat /\ (exists l, v = mk o l) /\
  (((d < 32)%nat -> wlater d o <= 0) -> wbnd d v (length r) (length (bb :: y))).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros f d o bb y ok v r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  apply Nat.ltb_ge in Ed. unfold MAXD in Ed.
  assert (Hd : (d < 32)%nat) by lia.
  cbn [tl] in H. cbv zeta in H. cbn [length].
  assert (LOOP : forall z, (length z <= length y)%nat ->
      jrl sm f (S d) o 0%nat 0%nat [] z ok = (Some (v, r), tr, ok') ->
      (length r < S (length y))%nat /\ (exists l, v = mk o l) /\
      (((d < 32)%nat -> wlater d o <= 0) -> wbnd d v (length r) (S (length y)))).
  { intros z Hz HL'.
    destruct (IHl d o 0%nat 0%nat [] z ok v r tr ok' Hd HL') as (nw & Hne & Hv & Hr & B).
    cbn [rev app] in Hv. subst v.
    assert (Hn1 : (1 <= length nw)%nat) by (destruct nw; [contradiction | cbn [length]; lia]).
    pose proof (wv_mk true o d nw Hne) as Mk. unfold Lw in Mk.
    pose proof (cwt_le (length nw) Hn1) as Cw.
    pose proof (kwt_le (length nw) Hn1) as Kw.
    pose proof (bm _ _ Hz) as Mz.
    pose proof (wsum_mk W o nw) as Sw.
    split; [lia|]. split; [exists nw; reflexivity|].
    intros Hlat'. specialize (B (Hlat' Hd)).
    unfold wbnd, wkch, Bw, wcb, wfirst in *. unfold indl in *. cbn [Nat.eqb] in *.
    destruct o; cbn [mk] in *; cbv beta iota in *; rewrite Sw, Mk; lia. }
  destruct (skip y) as [|ch r0] eqn:Ey; cbv beta iota in H.
  { exact (LOOP [] ltac:(cbn [length]; lia) H). }
  destruct (ch =? closer o); cbv beta iota in H.
  2: { exact (LOOP (ch :: r0) ltac:(rewrite <- Ey; exact (skip_len y)) H). }
  unfold jret in H. injection H as Hv Hr _ _. subst v r.
  pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
  pose proof (bm (S (length r0)) (length y) Hy) as M1.
  pose proof (wv_mk0 true o d) as M0.
  assert (S0 : wsum W (mk o []) = 0).
  { rewrite (wsum_mk W o []). unfold cwt, kwt, wl. cbn [length map fold_right]. destruct o; reflexivity. }
  split; [lia|]. split; [exists []; reflexivity|]. intros _.
  unfold wbnd, wcb in *. destruct o; cbn [mk map] in *; cbv beta iota in *;
    rewrite S0, M0; lia.
Qed.

(* ---- one value ---- *)

Lemma val_k : forall f, KRL f -> forall d x ok v r tr ok',
  jrv sm (S f) d x ok = (Some (v, r), tr, ok') ->
  (length r < length x)%nat /\ wbnd' d v (length r) (length x).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros f IHl d x ok v r tr ok' H. cbn [jrv] in H.
  destruct (skip x) as [|bb y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  pose proof (skip_len x) as Hs'. rewrite Ex in Hs'.
  assert (Fin : (length r < length (bb :: y))%nat /\ wbnd' d v (length r) (length (bb :: y)) ->
      (length r < length x)%nat /\ wbnd' d v (length r) (length x)).
  { intros [A1 A2]. pose proof (bm _ _ Hs') as M. split; [lia|].
    unfold wbnd', wbnd in A2 |- *.
    destruct v; cbv beta iota in A2 |- *; try lia;
      (intros Hp; specialize (A2 Hp); destruct A2 as [A3 A4]; split; [exact A3 | lia]). }
  apply Fin. clear Fin.
  (* a container: cont_k gives its shape without any numeric fact, and its bound once the fact for its
     kind is given, which is what wbnd' asks for *)
  assert (CONT : forall o, jr_cont (jrl sm f) d o (bb :: y) ok = (Some (v, r), tr, ok') ->
      (length r < length (bb :: y))%nat /\ wbnd' d v (length r) (length (bb :: y))).
  { intros o Hc'. destruct (cont_k f d o bb y ok v r tr ok' IHl Hc') as (L1 & (l & ->) & Bd).
    split; [exact L1|]. unfold wbnd'. destruct o; cbn [mk] in *; cbv beta iota in *; exact Bd. }
  destruct (bb =? 123); cbv beta iota in H; [exact (CONT true H)|].
  destruct (bb =? 91); cbv beta iota in H; [exact (CONT false H)|].
  pose proof wtl_lb as LB.
  destruct (bb =? 34); cbv beta iota in H.
  { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & _).
    pose proof (jr_string_spec y ok) as Hsp. rewrite Hj in Hsp. destruct Hsp as (q & _ & Hd & _ & Hl).
    cbv beta iota in H. unfold jret in H. injection H as Hv Hr _ _. subst v r1.
    pose proof (dec_k y s r Hd) as D.
    pose proof (swt_bnd (length s)) as S1.
    pose proof (fme_ge s) as F1.
    pose proof (cm (Z.of_nat (length s)) (Z.of_nat (length (flat_map ech s))) ltac:(lia)) as C1.
    pose proof (bm (length s + length r + 1) (length y) D) as B1.
    split; [cbn [length]; lia|].
    unfold wbnd', wbnd. cbv beta iota. rewrite (wv_str d s). cbn [wsum length]. lia. }
  destruct (bb =? 116); cbv beta iota in H.
  { destruct (lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_true in Hl. cbn [length] in Hl.
    assert (E4 : Wv true d JTrue = 4) by reflexivity.
    pose proof (bm (length r + 4) (length (bb :: y)) ltac:(cbn [length]; lia)) as B1.
    cbn [length] in B1 |- *.
    split; [lia|]. unfold wbnd', wbnd. cbv beta iota. rewrite E4. cbn [wsum]. lia. }
  destruct (bb =? 102); cbv beta iota in H.
  { destruct (lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_false in Hl. cbn [length] in Hl.
    assert (E5 : Wv true d JFalse = 5) by reflexivity.
    pose proof (bm (length r + 5) (length (bb :: y)) ltac:(cbn [length]; lia)) as B1.
    cbn [length] in B1 |- *.
    split; [lia|]. unfold wbnd', wbnd. cbv beta iota. rewrite E5. cbn [wsum]. lia. }
  destruct (bb =? 110); cbv beta iota in H.
  { destruct (lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_null in Hl. cbn [length] in Hl.
    assert (E4 : Wv true d JNull = 4) by reflexivity.
    pose proof (bm (length r + 4) (length (bb :: y)) ltac:(cbn [length]; lia)) as B1.
    cbn [length] in B1 |- *.
    split; [lia|]. unfold wbnd', wbnd. cbv beta iota. rewrite E4. cbn [wsum]. lia. }
  destruct (num_w _ _ _ _ _ _ _ H) as (txt & bits & -> & H1 & Hl).
  cbn [length] in Hl.
  pose proof (nwt_bnd (length txt) H1) as N1.
  pose proof (bm (length txt + length r) (S (length y)) ltac:(lia)) as B1.
  cbn [length].
  split; [lia|]. unfold wbnd', wbnd. cbv beta iota. rewrite (wv_num d txt bits). cbn [wsum]. lia.
Qed.

(* ---- the induction over the parse ---- *)

Lemma k_fuel : forall f,
  (forall d x ok v r tr ok', (1 <= d)%nat -> (d <= 32)%nat ->
     jrv sm f d x ok = (Some (v, r), tr, ok') ->
     (length r < length x)%nat /\
     wsum W v + b * Z.of_nat (length r) <= b * Z.of_nat (length x) + c * Wv true d v + al d) /\
  KRL f.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  induction f as [|f [IHv IHl]].
  - split; [|unfold KRL]; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok v r tr ok' Hd1 Hd2 H.
      destruct (val_k f IHl d x ok v r tr ok' H) as [Hlen Hv].
      split; [exact Hlen|].
      pose proof (HL d Hd2) as HLd. pose proof wtl_lb as LB.
      unfold wbnd', wbnd in Hv.
      destruct v; cbv beta iota in Hv; try lia.
      * specialize (Hv (fun Hlt => HIa d Hd1 Hlt)). destruct Hv as [Hlt Hb'].
        pose proof (HA d Hlt) as HAd. unfold wcb in Hb'. lia.
      * specialize (Hv (fun Hlt => HIo d Hlt)). destruct Hv as [Hlt Hb'].
        pose proof (HO d Hlt) as HOd. unfold wcb in Hb'. lia.
    + unfold KRL. intros d o n cap acc y ok v r tr ok' Hd H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      destruct (IHv (S d) y1 ok2 v0 r0 tv ok3 ltac:(lia) ltac:(lia) Ev) as (Hr0 & Bv).
      destruct (name_bnd o y ok1 nm y1 tn ok2 En) as (Ny & Np).
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|ch r1] eqn:Er; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      pose proof (bm (S (length r1)) (length r0) Hsr) as M1.
      destruct (ch =? 44); cbv beta iota in H.
      { destruct (IHl d o (S n) cap1 ((nm, v0) :: acc) r1 ok3 v r t4 ok' Hd H)
          as (nw & Hne & Hv & Hr & B).
        exists ((nm, v0) :: nw). split; [discriminate|]. split.
        - rewrite Hv. cbn [rev]. rewrite <- app_assoc. reflexivity.
        - split; [lia|]. intros Hlat. specialize (B Hlat).
          rewrite wgo_cons, wl_cons.
          unfold mw, wkch, Bw, wlater in *. unfold indl in *.
          cbn [fst snd length] in *. cbn [Nat.eqb] in B.
          destruct o; cbv beta iota in *; destruct (Nat.eqb n 0); cbv beta iota in *; lia. }
      destruct (ch =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as Hv Hr _ _. subst v r.
      exists [(nm, v0)]. split; [discriminate|]. split; [cbn [rev]; reflexivity|].
      split; [lia|]. intros Hlat.
      rewrite wgo_cons, wgo_nil, wl_cons.
      unfold mw, wkch, Bw, wlater, wl in *. unfold indl in *.
      cbn [fst snd length map fold_right] in *.
      destruct o; cbv beta iota in *; destruct (Nat.eqb n 0); cbv beta iota in *; lia.
Qed.

(* ---- the root ---- *)

Lemma wlen_wv : forall t, wlen t true = Wv true 0%nat t + 1.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros t. unfold wlen, wdoc, wdpieces, Wv. change (Z.of_nat 0%nat) with 0. cbv beta iota.
  rewrite concat_app, length_app. cbn [concat app length]. lia.
Qed.

Lemma root_k : forall x t, json_read sm x = Some t ->
  exists r : list Z, wbnd' 0%nat t (length r) (length x).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. exists r.
  exact (proj2 (val_k (2 * length x)%nat (proj2 (k_fuel _)) 0%nat x [] t' r tr ok' E)).
Qed.

(* ---- the live trees at RT3: the doc read p times and its copy 3 - p times, against the copy's
   pretty length ----
   The copy sets one root member: in place (its value replaced by a string) or appended. The copies do
   not use the input bytes of the replaced value, so (3 - p) b per such byte pays that value's p-fold
   weight and p-fold pretty text (at most 56 bytes per input byte, SlotSizes' rate), which the copy has
   not. At RT3, p = 1 is the doc and two copies, and p = 2 is the doc twice and one copy. *)

Lemma kwt_S_le : forall n, (1 <= n)%nat -> kwt W (S n) <= w_k64 W * (Z.of_nat n - 1).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros n Hn. unfold kwt. destruct (Nat.leb 33 (S n)) eqn:E.
  - apply Nat.leb_le in E.
    assert (K : 0 <= w_k64 W * (Z.of_nat n - 2)) by (apply Z.mul_nonneg_nonneg; lia).
    replace (Z.of_nat n - 1) with (1 + (Z.of_nat n - 2)) by lia.
    rewrite Z.mul_add_distr_l, Z.mul_1_r. lia.
  - assert (K : 0 <= w_k64 W * (Z.of_nat n - 1)) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

Lemma kwt_mono : forall n, kwt W n <= kwt W (S n).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros n. unfold kwt.
  destruct (Nat.leb 33 n) eqn:E1; destruct (Nat.leb 33 (S n)) eqn:E2; try lia.
  apply Nat.leb_le in E1. apply Nat.leb_nle in E2. lia.
Qed.

(* an appended member: the doc's object of n members p times, the copy's of n + 1 members 3 - p times *)
Lemma kwtp_le : forall p n, 0 <= p <= 3 -> (1 <= n)%nat ->
  p * kwt W n + (3 - p) * kwt W (S n) <= 3 * (w_k64 W * (Z.of_nat n - 1)).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros p n Hp Hn. pose proof (kwt_mono n) as M. pose proof (kwt_S_le n Hn) as S1.
  assert (P1 : p * kwt W n <= p * kwt W (S n)) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

Lemma cwtp_le : forall p n m, 0 <= p <= 3 -> (1 <= n)%nat -> (1 <= m)%nat ->
  p * cwt W n + (3 - p) * cwt W m <= 3 * wtc.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros p n m Hp Hn Hm. pose proof (cwt_le n Hn) as C1. pose proof (cwt_le m Hm) as C2.
  assert (P1 : p * cwt W n <= p * wtc) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (P2 : (3 - p) * cwt W m <= (3 - p) * wtc) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

(* a replaced value: the doc's value v0 read p times, plus its replacement rv read 3 - p times, fits
   three times the replacement's own bound on the doc's slice of v0 *)
Lemma jv_rep : forall p f e y1 ok v0 r0 tv ok' rv, 0 <= p <= 3 -> (1 <= e)%nat -> (e <= 32)%nat ->
  jrv sm f e y1 ok = (Some (v0, r0), tv, ok') ->
  56 * p * c - (3 - p) * b <= 0 ->
  56 * p * c - (3 - p) * b + p * c * G e + (3 - p) * wsum W rv <=
    3 * c * Wv true e rv + (3 - p) * al e ->
  p * wsum W v0 + (3 - p) * wsum W rv + 3 * b * Z.of_nat (length r0) <=
    3 * b * Z.of_nat (length y1) + 3 * c * Wv true e rv + 3 * al e.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros p f e y1 ok v0 r0 tv ok' rv Hp He1 He2 Hj J1 J2.
  destruct (proj1 (k_fuel f) e y1 ok v0 r0 tv ok' He1 He2 Hj) as [Hr Bv].
  pose proof (wv_rate sm f e y1 ok v0 r0 tv ok' Hj) as Rt.
  assert (Pb : p * (wsum W v0 + b * Z.of_nat (length r0)) <=
               p * (b * Z.of_nat (length y1) + c * Wv true e v0 + al e))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (Pr : p * c * (Wv true e v0 + 56 * Z.of_nat (length r0)) <=
               p * c * (56 * Z.of_nat (length y1) + G e))
    by (apply Z.mul_le_mono_nonneg_l; [apply Z.mul_nonneg_nonneg; lia | lia]).
  pose proof (mul_nonpos_mono (56 * p * c - (3 - p) * b) 1
                (Z.of_nat (length y1) - Z.of_nat (length r0)) J1 ltac:(lia)) as Mn.
  lia.
Qed.

(* the loop over a container's items, read p times for the doc and 3 - p times for a copy that may
   replace some members' values by rv *)
Definition JL (p : Z) (rv : jv) (f : nat) : Prop := forall d o n cap acc y ok v r tr ok', (d < 32)%nat ->
  jrl sm f (S d) o n cap acc y ok = (Some (v, r), tr, ok') ->
  exists nw, nw <> [] /\ v = mk o (rev acc ++ nw) /\ (length r < length y)%nat /\
    forall nw', Forall2 (mrel rv) nw nw' -> wlater d o <= 0 -> 0 <= p <= 3 ->
      56 * p * c - (3 - p) * b <= 0 ->
      56 * p * c - (3 - p) * b + p * c * G (S d) + (3 - p) * wsum W rv <=
        3 * c * Wv true (S d) rv + (3 - p) * al (S d) ->
      p * wl W o nw + (3 - p) * wl W o nw' + 3 * wkch o n (length nw) + 3 * b * Z.of_nat (length r) <=
        3 * b * Z.of_nat (length y) + 3 * c * Z.of_nat (length (concat (wgo true o d n nw'))) +
        3 * Bw d o n.

Lemma jl_fuel : forall p rv f, JL p rv f.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros p rv. induction f as [|f IHl].
  - unfold JL. intros. cbn [jrl] in *. unfold jrefuse in *. discriminate.
  - unfold JL. intros d o n cap acc y ok v r tr ok' Hd H. cbn [jrl] in H.
    apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
    apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
    apply jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
    destruct (proj1 (k_fuel f) (S d) y1 ok2 v0 r0 tv ok3 ltac:(lia) ltac:(lia) Ev) as (Hr0 & Bv).
    destruct (name_bnd o y ok1 nm y1 tn ok2 En) as (Ny & Np).
    pose proof (skip_len r0) as Hsr.
    destruct (skip r0) as [|ch r1] eqn:Er; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
    cbn [length] in Hsr.
    pose proof (bm (S (length r1)) (length r0) Hsr) as M1.
    destruct (ch =? 44); cbv beta iota in H.
    + destruct (IHl d o (S n) cap1 ((nm, v0) :: acc) r1 ok3 v r t4 ok' Hd H) as (nw & Hne & Hv & Hr & B).
      exists ((nm, v0) :: nw). split; [discriminate|]. split.
      { rewrite Hv. cbn [rev]. rewrite <- app_assoc. reflexivity. }
      split; [lia|].
      intros nw' F Hlat Hp J1 J2.
      destruct nw' as [|[nm' v0'] l1']; [inversion F|].
      inversion F as [|? ? ? ? Hm Fr].
      destruct Hm as [Hfst Hsnd]. cbn [fst snd] in Hfst, Hsnd. subst nm'.
      specialize (B l1' Fr Hlat Hp J1 J2).
      assert (JV : p * wsum W v0 + (3 - p) * wsum W v0' + 3 * b * Z.of_nat (length r0) <=
                   3 * b * Z.of_nat (length y1) + 3 * c * Wv true (S d) v0' + 3 * al (S d)).
      { destruct Hsnd as [-> | ->]; [lia|].
        exact (jv_rep p f (S d) y1 ok2 v0 r0 tv ok3 rv Hp ltac:(lia) ltac:(lia) Ev J1 J2). }
      rewrite wgo_cons, !wl_cons.
      unfold mw, wkch, Bw, wlater in *. unfold indl in *.
      cbn [fst snd length] in *. cbn [Nat.eqb] in B.
      destruct o; cbv beta iota in *; destruct (Nat.eqb n 0); cbv beta iota in *; lia.
    + destruct (ch =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as Hv Hr _ _. subst v r.
      exists [(nm, v0)]. split; [discriminate|]. split; [cbn [rev]; reflexivity|].
      split; [lia|].
      intros nw' F Hlat Hp J1 J2.
      destruct nw' as [|[nm' v0'] l1']; [inversion F|].
      inversion F as [|? ? ? ? Hm Fr].
      destruct l1'; [|inversion Fr].
      destruct Hm as [Hfst Hsnd]. cbn [fst snd] in Hfst, Hsnd. subst nm'.
      assert (JV : p * wsum W v0 + (3 - p) * wsum W v0' + 3 * b * Z.of_nat (length r0) <=
                   3 * b * Z.of_nat (length y1) + 3 * c * Wv true (S d) v0' + 3 * al (S d)).
      { destruct Hsnd as [-> | ->]; [lia|].
        exact (jv_rep p f (S d) y1 ok2 v0 r0 tv ok3 rv Hp ltac:(lia) ltac:(lia) Ev J1 J2). }
      rewrite wgo_cons, wgo_nil, !wl_cons.
      unfold mw, wkch, Bw, wlater, wl in *. unfold indl in *.
      cbn [fst snd length map fold_right] in *.
      destruct o; cbv beta iota in *; destruct (Nat.eqb n 0); cbv beta iota in *; lia.
Qed.

(* an object root is the empty object, or the item loop at depth 1 over input it does not exceed *)
Lemma root_loop : forall x ms, json_read sm x = Some (JObj ms) ->
  (ms = [] /\ (2 <= length x)%nat) \/
  (exists f (z r : list Z) tr ok', (S (length z) <= length x)%nat /\
     jrl sm f 1 true 0 0 [] z [] = (Some (JObj ms, r), tr, ok')).
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros x ms H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as Ht; subst t'|discriminate].
  unfold jr_value in E. cbn [jrv] in E.
  destruct (skip x) as [|bb y] eqn:Ex; cbv beta iota in E; [unfold jrefuse in E; discriminate|].
  pose proof (skip_len x) as Hs'. rewrite Ex in Hs'. cbn [length] in Hs'.
  destruct (bb =? 123); cbv beta iota in E.
  { unfold jr_cont in E. cbn [Nat.ltb MAXD tl] in E. cbv beta iota zeta in E.
    pose proof (skip_len y) as Hy.
    destruct (skip y) as [|ch r0] eqn:Ey; cbv beta iota in E.
    - right. exists (2 * length x)%nat, [], r, tr, ok'. split; [cbn [length]; lia | exact E].
    - destruct (ch =? closer true); cbv beta iota in E.
      + unfold jret in E. injection E as Hm _ _ _. subst ms.
        left. split; [reflexivity|]. cbn [length] in Hy. lia.
      + right. exists (2 * length x)%nat, (ch :: r0), r, tr, ok'.
        split; [cbn [length] in Hy |- *; lia | exact E]. }
  destruct (bb =? 91); cbv beta iota in E.
  { destruct (cont_k (2 * length x)%nat 0%nat false bb y [] (JObj ms) r tr ok'
                (proj2 (k_fuel _)) E) as (_ & (l & Hl) & _).
    cbn [mk] in Hl. discriminate Hl. }
  destruct (bb =? 34); cbv beta iota in E.
  { apply jbind_some in E as ([s r1] & t1 & ok1 & t2 & _ & E & _).
    cbv beta iota in E. unfold jret in E. discriminate E. }
  destruct (bb =? 116); cbv beta iota in E.
  { destruct (lit_w _ _ _ _ _ _ _ _ E) as [Hv _]. discriminate Hv. }
  destruct (bb =? 102); cbv beta iota in E.
  { destruct (lit_w _ _ _ _ _ _ _ _ E) as [Hv _]. discriminate Hv. }
  destruct (bb =? 110); cbv beta iota in E.
  { destruct (lit_w _ _ _ _ _ _ _ _ E) as [Hv _]. discriminate Hv. }
  destruct (num_w _ _ _ _ _ _ _ E) as (txt & bits & Hv & _). discriminate Hv.
Qed.

(* the constant of the joint bound: the empty doc, a copy set in place, a copy appended to *)
Definition e_live (p : Z) (MK MV : list Z) : Z :=
  Z.max ((3 - p) * wsum W (JObj [(MK, JStr MV)]) - 6 * b - 3 * c * wlen (JObj [(MK, JStr MV)]) true)
 (Z.max (3 * wfirst 0 true - 3 * c)
        (3 * wfirst 0 true - 3 * c + (3 - p) * mw W true (MK, JStr MV) -
         3 * c * (1 + indl true 1 + NP true true MK + Wv true 1 (JStr MV)))).

Theorem wt_live : forall p MK MV x ms, json_read sm x = Some (JObj ms) -> 0 <= p <= 3 ->
  56 * p * c - (3 - p) * b <= 0 ->
  56 * p * c - (3 - p) * b + p * c * G 1 + (3 - p) * wsum W (JStr MV) <=
    3 * c * Wv true 1 (JStr MV) + (3 - p) * al 1 ->
  p * wsum W (JObj ms) + (3 - p) * wsum W (JObj (pj_set_model ms MK (JStr MV))) <=
    3 * b * Z.of_nat (length x) + 3 * c * wlen (JObj (pj_set_model ms MK (JStr MV))) true +
    e_live p MK MV.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo.
  intros p MK MV x ms H Hp J1 J2.
  destruct (root_loop x ms H) as [[-> Hx] | (f & z & r & tr & ok' & Hz & HL')].
  - cbn [pj_set_model].
    assert (S0 : wsum W (JObj []) = 0) by reflexivity.
    pose proof (bm 2 (length x) Hx) as B2.
    rewrite S0. unfold e_live. lia.
  - destruct (jl_fuel p (JStr MV) f 0%nat true 0%nat 0%nat [] z [] (JObj ms) r tr ok' ltac:(lia) HL')
      as (nw & Hne & Hv & Hr & B).
    cbn [rev app mk] in Hv. injection Hv as Hv. subst nw.
    assert (Hn1 : (1 <= length ms)%nat) by (destruct ms; [contradiction | cbn [length]; lia]).
    pose proof (bm (S (length z)) (length x) Hz) as Bz.
    pose proof (HIo 0%nat ltac:(lia)) as Hlat.
    pose proof (wsum_mk W true ms) as Sd. cbn [mk] in Sd.
    pose proof (cwt_le (length ms) Hn1) as Cw.
    destruct (set_cases ms MK (JStr MV)) as [Ha | Hi].
    + (* appended *)
      rewrite Ha.
      specialize (B ms (mrel_refl _ ms) Hlat Hp J1 J2).
      assert (Hne' : ms ++ [(MK, JStr MV)] <> []) by (destruct ms; discriminate).
      pose proof (wsum_mk W true (ms ++ [(MK, JStr MV)])) as Sc. cbn [mk] in Sc.
      rewrite length_app, wl_app1 in Sc. cbn [length] in Sc. rewrite Nat.add_1_r in Sc.
      pose proof (wv_mk true true 0 (ms ++ [(MK, JStr MV)]) Hne') as Mk. cbn [mk] in Mk. unfold Lw in Mk.
      rewrite wgo_app1 in Mk. cbn [fst snd] in Mk.
      replace (Nat.eqb (0 + length ms) 0) with false in Mk
        by (destruct ms; [contradiction | reflexivity]).
      cbv beta iota in Mk.
      pose proof (wlen_wv (JObj (ms ++ [(MK, JStr MV)]))) as Wl.
      pose proof (cwtp_le p (length ms) (S (length ms)) Hp Hn1 ltac:(lia)) as C2.
      pose proof (kwtp_le p (length ms) Hp Hn1) as K2.
      rewrite Wl, Mk, Sd, Sc. unfold e_live, wkch, Bw, wfirst in *. unfold indl in *.
      cbn [Nat.eqb] in B. cbv beta iota in *. lia.
    + (* in place *)
      specialize (B _ Hi Hlat Hp J1 J2).
      pose proof (Forall2_length Hi) as Hlen.
      assert (Hne' : pj_set_model ms MK (JStr MV) <> []).
      { intros E0. rewrite E0 in Hlen. cbn [length] in Hlen. lia. }
      pose proof (wsum_mk W true (pj_set_model ms MK (JStr MV))) as Sc. cbn [mk] in Sc.
      rewrite <- Hlen in Sc.
      pose proof (wv_mk true true 0 (pj_set_model ms MK (JStr MV)) Hne') as Mk. cbn [mk] in Mk.
      unfold Lw in Mk.
      pose proof (wlen_wv (JObj (pj_set_model ms MK (JStr MV)))) as Wl.
      pose proof (kwt_le (length ms) Hn1) as K1.
      rewrite Wl, Mk, Sd, Sc. unfold e_live, wkch, Bw, wfirst in *. unfold indl in *.
      cbn [Nat.eqb] in B. cbv beta iota in *. lia.
Qed.

(* the root's own facts, declared here so that the machine above does not depend on them *)
Hypothesis HIa0 : wlater 0%nat false <= 0.          (* an ARRAY root's later items *)

Theorem wt_read : forall x t, json_read sm x = Some t ->
  wsum W t <= b * Z.of_nat (length x) + c * wlen t true + al 0%nat.
Proof using sm W b c al Hb Hc Hk Hwl HT HL HA HO HIa HIo HIa0.
  intros x t H. destruct (root_k x t H) as (r & V).
  rewrite (wlen_wv t).
  assert (Hr : 0 <= b * Z.of_nat (length r)) by (apply Z.mul_nonneg_nonneg; [exact Hb | lia]).
  assert (Hcw : 0 <= c * Wv true 0%nat t).
  { apply Z.mul_nonneg_nonneg; [exact Hc|]. unfold Wv. lia. }
  pose proof (HL 0%nat ltac:(lia)) as HL0. pose proof wtl_lb as LB.
  unfold wbnd', wbnd in V.
  destruct t; cbv beta iota in V; try lia.
  - specialize (V (fun _ => HIa0)). destruct V as [Hlt Hb'].
    pose proof (HA 0%nat Hlt) as HA0. unfold wcb in Hb'. lia.
  - specialize (V (fun Hlt => HIo 0%nat Hlt)). destruct V as [Hlt Hb'].
    pose proof (HO 0%nat Hlt) as HO0. unfold wcb in Hb'. lia.
Qed.

Hypothesis HOo : wfirst 0%nat true <= alo 0%nat.    (* an OBJECT root *)
Hypothesis HEo : -2 * b - 2 * c <= alo 0%nat.       (* an empty object root *)

Theorem wt_read_obj : forall x ms, json_read sm x = Some (JObj ms) ->
  wsum W (JObj ms) <= b * Z.of_nat (length x) + c * wlen (JObj ms) true + alo 0%nat.
Proof using sm W b c al alo Hb Hc Hk Hwl HT HL HA HO HIa HIo HOo HEo.
  intros x ms H. destruct (root_k x (JObj ms) H) as (r & V).
  rewrite (wlen_wv (JObj ms)).
  assert (Hr : 0 <= b * Z.of_nat (length r)) by (apply Z.mul_nonneg_nonneg; [exact Hb | lia]).
  assert (Hcw : 0 <= c * Wv true 0%nat (JObj ms)).
  { apply Z.mul_nonneg_nonneg; [exact Hc|]. unfold Wv. lia. }
  unfold wbnd', wbnd in V. cbv beta iota in V.
  specialize (V (fun Hlt => HIo 0%nat Hlt)). destruct V as [_ Hb']. unfold wcb in Hb'. lia.
Qed.

End WT.

(* ------------------------------------------------------------------ *)
(* the instances: each table is checked by vm_compute                  *)
(* ------------------------------------------------------------------ *)

Lemma seq_all : forall (P : nat -> bool) (s n : nat),
  forallb P (seq s n) = true -> forall d, (s <= d)%nat -> (d < s + n)%nat -> P d = true.
Proof.
  intros P s n H d H1 H2. rewrite forallb_forall in H. apply H, in_seq. lia.
Qed.

(* every numeric fact the machine needs of (W, b, c, al), as one finite check *)
Definition wt_ok (W : nweights) (b c : Z) (al : nat -> Z) : bool :=
  (0 <=? b) && (0 <=? c) && (0 <=? w_k64 W) && (w_len W <=? b) && Nat.leb 432 (w_lmin W) &&
  forallb (fun d => wtl W b c <=? al d) (seq 0 33) &&
  forallb (fun d => (wfirst W b c al d false <=? al d) && (wfirst W b c al d true <=? al d)) (seq 0 32) &&
  forallb (fun d => wlater W b c al d false <=? 0) (seq 1 31) &&
  forallb (fun d => wlater W b c al d true <=? 0) (seq 0 32).

(* the facts wt_ok yields, as the machine states them *)
Lemma wt_ok_hyps : forall W b c al, wt_ok W b c al = true ->
  0 <= b /\ 0 <= c /\ 0 <= w_k64 W /\ w_len W <= b /\ (432 <= w_lmin W)%nat /\
  (forall d, (d <= 32)%nat -> wtl W b c <= al d) /\
  (forall d, (d < 32)%nat -> wfirst W b c al d false <= al d) /\
  (forall d, (d < 32)%nat -> wfirst W b c al d true <= al d) /\
  (forall d, (1 <= d)%nat -> (d < 32)%nat -> wlater W b c al d false <= 0) /\
  (forall d, (d < 32)%nat -> wlater W b c al d true <= 0).
Proof.
  intros W b c al Hok. unfold wt_ok in Hok.
  apply andb_true_iff in Hok as [Hok Hq9].
  apply andb_true_iff in Hok as [Hok Hq8].
  apply andb_true_iff in Hok as [Hok Hq7].
  apply andb_true_iff in Hok as [Hok Hq6].
  apply andb_true_iff in Hok as [Hok Hq5].
  apply andb_true_iff in Hok as [Hok Hq4].
  apply andb_true_iff in Hok as [Hok Hq3].
  apply andb_true_iff in Hok as [Hq1 Hq2].
  split; [apply Z.leb_le; exact Hq1|].
  split; [apply Z.leb_le; exact Hq2|].
  split; [apply Z.leb_le; exact Hq3|].
  split; [apply Z.leb_le; exact Hq4|].
  split; [apply Nat.leb_le; exact Hq5|].
  split; [intros d Hd; apply Z.leb_le; exact (seq_all _ 0 33 Hq6 d ltac:(lia) ltac:(lia))|].
  split.
  { intros d Hd. apply Z.leb_le.
    pose proof (seq_all _ 0 32 Hq7 d ltac:(lia) ltac:(lia)) as K.
    apply andb_true_iff in K as [K1 _]. exact K1. }
  split.
  { intros d Hd. apply Z.leb_le.
    pose proof (seq_all _ 0 32 Hq7 d ltac:(lia) ltac:(lia)) as K.
    apply andb_true_iff in K as [_ K2]. exact K2. }
  split.
  { intros d Hd1 Hd2. apply Z.leb_le. exact (seq_all _ 1 31 Hq8 d ltac:(lia) ltac:(lia)). }
  intros d Hd. apply Z.leb_le. exact (seq_all _ 0 32 Hq9 d ltac:(lia) ltac:(lia)).
Qed.

Lemma wt_ok_read : forall sm W b c al x t,
  wt_ok W b c al = true -> wlater W b c al 0%nat false <= 0 ->
  json_read sm x = Some t -> wsum W t <= b * Z.of_nat (length x) + c * wlen t true + al 0%nat.
Proof.
  intros sm W b c al x t Hok H0 H.
  destruct (wt_ok_hyps W b c al Hok) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  exact (wt_read sm W b c al A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 H0 x t H).
Qed.

(* an OBJECT root: it needs no fact about an array root's later items, which instance 1 has not got *)
Lemma wt_ok_read_obj : forall sm W b c al alo0 x ms,
  wt_ok W b c al = true ->
  wfirst W b c al 0%nat true <= alo0 -> -2 * b - 2 * c <= alo0 ->
  json_read sm x = Some (JObj ms) ->
  wsum W (JObj ms) <= b * Z.of_nat (length x) + c * wlen (JObj ms) true + alo0.
Proof.
  intros sm W b c al alo0 x ms Hok Ho He H.
  destruct (wt_ok_hyps W b c al Hok) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (A11 : wfirst W b c al 0%nat true <= (fun _ : nat => alo0) 0%nat) by (cbv beta; lia).
  assert (A12 : -2 * b - 2 * c <= (fun _ : nat => alo0) 0%nat) by (cbv beta; lia).
  exact (wt_read_obj sm W b c al (fun _ : nat => alo0)
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 x ms H).
Qed.

(* ---- instance 1 (RT3): an object root ---- *)

Definition W_rt3 : nweights :=
  {| w_c18 := 20910; w_c9 := 20910; w_k64 := 20910; w_str := 20910; w_num := 20910;
     w_len := 9129; w_lmin := 4096 |}.

Definition al_rt3 (d : nat) : Z :=
  nth d [14093; 11645; 9333; 7157; 5117; 3213; 1445; -187; -1683; -3043; -4267; -5355; -6307;
         -7123; -7803; -8347; -8755; -9027] (-9163).

Corollary wt_rt3 : forall sm x ms, json_read sm x = Some (JObj ms) ->
  wsum W_rt3 (JObj ms) <= 9129 * Z.of_nat (length x) + 34 * wlen (JObj ms) true + (-13430).
Proof.
  intros sm x ms H.
  apply (wt_ok_read_obj sm W_rt3 9129 34 al_rt3 (-13430) x ms); [vm_compute; reflexivity | | | exact H].
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.

(* the three live trees at RT3, the doc and twice its copy, against the copy's pretty length; the
   constant is the empty doc's: {} (2 bytes) whose copy is the one-member object of weight 20910 *)
Corollary wt_rt3_live : forall sm x ms, json_read sm x = Some (JObj ms) ->
  wsum W_rt3 (JObj ms) + 2 * wsum W_rt3 (PresetReqAt.copy_set ms) <=
    3 * 9129 * Z.of_nat (length x) + 102 * wlen (PresetReqAt.copy_set ms) true + (-17340).
Proof.
  intros sm x ms H. unfold PresetReqAt.copy_set.
  destruct (wt_ok_hyps W_rt3 9129 34 al_rt3 ltac:(vm_compute; reflexivity))
    as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof (wt_live sm W_rt3 9129 34 al_rt3 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 1
                PresetReqAt.MOD_KEY PresetReqAt.MOD_VAL x ms H ltac:(lia)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as K.
  assert (E : e_live W_rt3 9129 34 al_rt3 1 PresetReqAt.MOD_KEY PresetReqAt.MOD_VAL = -17340)
    by (vm_compute; reflexivity).
  rewrite E in K. lia.
Qed.

(* the same live trees as D3 counts them: the doc twice (pj_set mutates the second parse in place and
   keeps its blocks) and the read-back copy once, against the copy's pretty length. The replaced old
   value counts twice and has no pretty text in the copy; its 2 c * 56 = 3808 <= b per input byte, which
   the copy does not spend, pays that. The constant is again the empty doc's: {} whose copy weighs
   20910 once, 20910 - 3 * 9129 * 2 - 102 * 43 = -38250 *)
Corollary wt_rt3_live2 : forall sm x ms, json_read sm x = Some (JObj ms) ->
  2 * wsum W_rt3 (JObj ms) + wsum W_rt3 (PresetReqAt.copy_set ms) <=
    3 * 9129 * Z.of_nat (length x) + 102 * wlen (PresetReqAt.copy_set ms) true + (-38250).
Proof.
  intros sm x ms H. unfold PresetReqAt.copy_set.
  destruct (wt_ok_hyps W_rt3 9129 34 al_rt3 ltac:(vm_compute; reflexivity))
    as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof (wt_live sm W_rt3 9129 34 al_rt3 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 2
                PresetReqAt.MOD_KEY PresetReqAt.MOD_VAL x ms H ltac:(lia)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as K.
  assert (E : e_live W_rt3 9129 34 al_rt3 2 PresetReqAt.MOD_KEY PresetReqAt.MOD_VAL = -38250)
    by (vm_compute; reflexivity).
  rewrite E in K. lia.
Qed.

(* ---- instance 2 (RT2): any root ---- *)

Definition W_rt2 : nweights :=
  {| w_c18 := 10000; w_c9 := 10000; w_k64 := 10000; w_str := 10000; w_num := 10000;
     w_len := 4579; w_lmin := 4096 |}.

Definition al_rt2 (d : nat) : Z :=
  nth d [923; 165; -537; -1183; -1773; -2307; -2785; -3207; -3573; -3883; -4137; -4335; -4477; -4563]
    (-4593).

Corollary wt_rt2 : forall sm x t, json_read sm x = Some t ->
  wsum W_rt2 t <= 4579 * Z.of_nat (length x) + 14 * wlen t true + 923.
Proof.
  intros sm x t H.
  apply (wt_ok_read sm W_rt2 4579 14 al_rt2 x t); [vm_compute; reflexivity | | exact H].
  vm_compute. discriminate.
Qed.

(* ---- instance 2' (RT2, the tighter certificate): any root ---- *)

Definition W_rt2b : nweights :=
  {| w_c18 := 100000; w_c9 := 100000; w_k64 := 100000; w_str := 100000; w_num := 100000;
     w_len := 44310; w_lmin := 4096 |}.

Definition al_rt2b (d : nat) : Z :=
  nth d [55264; 44760; 34840; 25504; 16752; 8584; 1000; -6000; -12416; -18248; -23496; -28160;
         -32240; -35736; -38648; -40976; -42720; -43880] (-44456).

Corollary wt_rt2b : forall sm x t, json_read sm x = Some t ->
  wsum W_rt2b t <= 44310 * Z.of_nat (length x) + 146 * wlen t true + 55264.
Proof.
  intros sm x t H.
  apply (wt_ok_read sm W_rt2b 44310 146 al_rt2b x t); [vm_compute; reflexivity | | exact H].
  vm_compute. discriminate.
Qed.

(* ---- instance 3 (no flush): any root, c = 0 ----
   w_len is 92, not b = 93: with c = 0 a number of w_lmin digits has no pretty text to pay its w_num, and
   only its comma (b) to spare, so w_len = b = 93 is FALSE (an array of m such numbers exceeds any
   constant by 99 m). *)

Definition W_nf : nweights :=
  {| w_c18 := 192; w_c9 := 128; w_k64 := 192; w_str := 192; w_num := 192;
     w_len := 92; w_lmin := 4096 |}.

Definition al_nf (d : nat) : Z :=
  nth d [99; 93; 87; 81; 75; 69; 63; 57; 51; 45; 39; 33; 27; 21; 15; 9;
         3; -3; -9; -15; -21; -27; -33; -39; -45; -51; -57; -63; -69; -75; -81; -87] (-93).

Corollary wt_nf : forall sm x t, json_read sm x = Some t ->
  wsum W_nf t <= 93 * Z.of_nat (length x) + 99.
Proof.
  intros sm x t H.
  assert (K : wsum W_nf t <= 93 * Z.of_nat (length x) + 0 * wlen t true + 99).
  { apply (wt_ok_read sm W_nf 93 0 al_nf x t); [vm_compute; reflexivity | | exact H].
    vm_compute. discriminate. }
  lia.
Qed.
