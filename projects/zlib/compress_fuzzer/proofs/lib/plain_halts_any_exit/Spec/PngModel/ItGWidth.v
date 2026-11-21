(** * ItGWidth — [P1] zr_width_covers DERIVED from zr_ptr_children +
    canonical prefix-freeness.  NO it_subsz walk.

    OWNER: an earlier development run.  Route discovery 2026-08-21: if a code [cw] whose
    first [root] bits select window [i] were longer than [root + op],
    then the [op] bits after the root prefix name a child [j] of the
    pointer (write_bits is surjective onto op-bit strings), and
    [zr_ptr_children] hands that child a FULL code [cw'] of length at
    most [root + op] that is then a strict PREFIX of [cw] — impossible
    for two distinct canonical codes.  Same subsumption shape as the
    no_child_markers re-scope: q4's positive child-ownership conjunct
    already carries the width fact.

    The pairwise prefix-free fact is a PREMISE here, so this file needs
    only Base/Bits/Huff; the assembly discharges it from the B3 head's
    own PreGo via InftreesBridge (it_pre_go_inv +
    it_accept_codes_prefix_free_of_lengths — both landed).

    Prop texts VERBATIM from B3B5Stmts.v
    (), duplicated only until the round
    decides that file's landing home, then these become Requires.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff ItGClassHead.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.
(* Home re-point (q7 freeze v41, homes follow landing order):
   [zr_ptr_children] comes from its landed home ItGClassHead;
   the local duplicate this file carried until the ruling is DROPPED. *)

(* ------------------------------------------------------------------ *)
(* Frozen ownership vocabulary (B3B5Stmts.v , verbatim).       *)

Definition zr_width_covers (lens : list nat) (root i op : Z) : Prop :=
  forall sym cw, code_for lens 15%nat sym = Some cw ->
    firstn (Z.to_nat root) cw = write_bits (Z.to_nat root) i ->
    Z.of_nat (length cw) <= root + op.

(* ------------------------------------------------------------------ *)
(* Two list/bit facts the tree does not carry.                         *)

(** [firstn] splits over [+].  Stdlib-only; named with a prefix to stay
    clear of any future stdlib [firstn_plus]. *)
Lemma wb_firstn_plus : forall (A : Type) (n m : nat) (l : list A),
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction n as [|k IH]; intros m l; [reflexivity|].
  destruct l as [|a l']; cbn [firstn skipn Nat.add app].
  - now rewrite firstn_nil.
  - now rewrite IH.
Qed.

(** Every bit string is written by exactly the value it denotes. *)
Lemma write_bits_surj : forall bs : list bool,
  exists v, 0 <= v < 2 ^ Z.of_nat (length bs)
            /\ write_bits (length bs) v = bs.
Proof.
  induction bs as [|b bs IH].
  - exists 0. split; [cbn; lia | reflexivity].
  - destruct IH as [v [Hv Hw]].
    exists ((if b then 1 else 0) + 2 * v).
    assert (Hodd : Z.odd ((if b then 1 else 0) + 2 * v) = b)
      by (rewrite Z.odd_add_mul_2; destruct b; reflexivity).
    assert (Hdiv : ((if b then 1 else 0) + 2 * v) / 2 = v).
    { replace ((if b then 1 else 0) + 2 * v)
        with (v * 2 + (if b then 1 else 0)) by ring.
      rewrite Z.div_add_l by lia.
      destruct b; [replace (1 / 2) with 0 by reflexivity
                  | replace (0 / 2) with 0 by reflexivity]; lia. }
    split.
    + cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      destruct b; lia.
    + cbn [length write_bits]. now rewrite Hodd, Hdiv, Hw.
Qed.

(* ------------------------------------------------------------------ *)
(* The derivation.                                                     *)

(** [P1].  A pointer whose children all own full codes cannot leave any
    same-prefix code longer than its width: the long code's
    [root+op]-bit truncation IS some child's full code, and canonical
    codes are prefix-free. *)
Lemma width_covers_of_children :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code)
         (i op val : Z),
    0 <= root ->
    0 <= op ->
    (forall s1 s2 cw1 cw2,
        code_for lens 15%nat s1 = Some cw1 ->
        code_for lens 15%nat s2 = Some cw2 ->
        s1 <> s2 ->
        is_prefix cw1 cw2 = false) ->
    zr_ptr_children T root lens ent i op val ->
    zr_width_covers lens root i op.
Proof.
  intros T root lens ent i op val Hroot Hop Hpf Hch sym cw Hcf Hpre.
  destruct (Z.le_gt_cases (Z.of_nat (length cw)) (root + op)) as [Hle|Hlong];
    [exact Hle | exfalso].
  (* the op bits of cw after the root prefix *)
  set (slice := firstn (Z.to_nat op) (skipn (Z.to_nat root) cw)).
  assert (Hsl : length slice = Z.to_nat op).
  { unfold slice. rewrite length_firstn, length_skipn. lia. }
  destruct (write_bits_surj slice) as [j [Hjr Hjw]].
  rewrite Hsl in Hjr, Hjw.
  rewrite Z2Nat.id in Hjr by exact Hop.
  destruct (Hch j Hjr) as (sym' & cw' & Hcf' & Hlen' & _ & _ & Hfull').
  rewrite Hjw in Hfull'.
  (* the (root+op)-bit truncation of cw is the child's window *)
  assert (Hsplit : firstn (Z.to_nat root + Z.to_nat op) cw
                   = write_bits (Z.to_nat root) i ++ slice).
  { rewrite wb_firstn_plus. unfold slice. now rewrite Hpre. }
  (* hence the child's full code is a prefix of cw *)
  assert (Hpref : firstn (length cw') cw = cw').
  { assert (Hmin : Init.Nat.min (length cw')
                     (Z.to_nat root + Z.to_nat op) = length cw') by lia.
    transitivity
      (firstn (length cw') (firstn (Z.to_nat root + Z.to_nat op) cw)).
    - now rewrite firstn_firstn, Hmin.
    - rewrite Hsplit. exact Hfull'. }
  (* distinct symbols: the lengths differ *)
  assert (Hne : sym' <> sym).
  { intro Heq. subst sym'. rewrite Hcf in Hcf'.
    injection Hcf' as Hcc. subst cw'. lia. }
  pose proof (Hpf sym' sym cw' cw Hcf' Hcf Hne) as Hnp.
  rewrite (is_prefix_of_firstn cw' cw Hpref) in Hnp. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Marker-arm derivations at the max==1 shape.                         *)
(* Frozen vocabulary (B3B5Stmts.v , verbatim), same rule as    *)
(* above: duplicated until the round decides the landing home.         *)

Definition zr_no_short_code (lens : list nat) (root i : Z) : Prop :=
  forall sym cw, code_for lens 15%nat sym = Some cw ->
    Z.of_nat (length cw) <= root ->
    firstn (length cw) (write_bits (Z.to_nat root) i) <> cw.

Definition zr_no_long_code_at (lens : list nat) (root i : Z) : Prop :=
  forall sym cw, code_for lens 15%nat sym = Some cw ->
    root < Z.of_nat (length cw) ->
    firstn (Z.to_nat root) cw <> write_bits (Z.to_nat root) i.

(** max==1, incomplete-but-accepted: ONE 1-bit code exists, so it is the
    canonical zero code [code_bits 0 1 = [false]]; the marker slot is
    i = 1 = [true], which no short code can match. *)
Lemma no_short_code_max1 :
  forall lens : list nat,
    count_len lens 1%nat = 1%nat ->
    zr_no_short_code lens 1 1.
Proof.
  intros lens Hc1 sym cw Hcf Hshort.
  destruct (code_for_inv lens 15%nat sym cw Hcf)
    as (len & Hn & Hge1 & _ & Hcw).
  assert (Hlcw : length cw = len) by (rewrite Hcw; apply code_bits_length).
  assert (Hlen1 : len = 1%nat) by lia.
  rewrite Hlen1 in Hn, Hcw.
  pose proof (code_offset_lt lens sym 1%nat Hn) as Hofs.
  rewrite Hc1 in Hofs.
  assert (Hofs0 : code_offset lens sym 1%nat = 0%nat) by lia.
  rewrite Hofs0 in Hcw.
  assert (Hnc1 : nc lens 1 = 0%nat) by reflexivity.
  rewrite Hnc1 in Hcw. cbn in Hcw. subst cw.
  cbn. discriminate.
Qed.

(** max==1: there IS no code longer than one bit, at any window. *)
Lemma no_long_code_max1 :
  forall (lens : list nat) (i : Z),
    (forall l : nat, (2 <= l <= 15)%nat -> count_len lens l = 0%nat) ->
    zr_no_long_code_at lens 1 i.
Proof.
  intros lens i Hh2 sym cw Hcf Hlong.
  exfalso.
  destruct (code_for_inv lens 15%nat sym cw Hcf)
    as (len & Hn & Hge1 & Hle15 & Hcw).
  assert (Hlcw : length cw = len) by (rewrite Hcw; apply code_bits_length).
  pose proof (code_offset_lt lens sym len Hn) as Hofs.
  rewrite (Hh2 len ltac:(lia)) in Hofs. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* PreEmpty vacuity: a length list with NO live counts has no codes,   *)
(* so both marker-arm Props hold at ANY (root, i) — the DIST           *)
(* accepted-EMPTY arm's two-marker table needs exactly this.           *)

Lemma code_for_none_of_zero_counts : forall (lens : list nat) sym cw,
  (forall l : nat, (1 <= l <= 15)%nat -> count_len lens l = 0%nat) ->
  code_for lens 15%nat sym = Some cw -> False.
Proof.
  intros lens sym cw Hz Hcf.
  destruct (code_for_inv lens 15%nat sym cw Hcf)
    as (len & Hn & Hge1 & Hle15 & _).
  pose proof (code_offset_lt lens sym len Hn) as Hofs.
  rewrite (Hz len ltac:(lia)) in Hofs. lia.
Qed.

Lemma no_short_code_none : forall (lens : list nat) (root i : Z),
  (forall l : nat, (1 <= l <= 15)%nat -> count_len lens l = 0%nat) ->
  zr_no_short_code lens root i.
Proof.
  intros lens root i Hz sym cw Hcf _.
  exfalso. exact (code_for_none_of_zero_counts lens sym cw Hz Hcf).
Qed.

Lemma no_long_code_none : forall (lens : list nat) (root i : Z),
  (forall l : nat, (1 <= l <= 15)%nat -> count_len lens l = 0%nat) ->
  zr_no_long_code_at lens root i.
Proof.
  intros lens root i Hz sym cw Hcf _.
  exfalso. exact (code_for_none_of_zero_counts lens sym cw Hz Hcf).
Qed.

(** Width and children are vacuous there too — the two-marker table has
    no pointer cells, but stating these keeps the assembly uniform if a
    disjunct ever routes through them. *)
Lemma width_covers_none : forall (lens : list nat) (root i op : Z),
  (forall l : nat, (1 <= l <= 15)%nat -> count_len lens l = 0%nat) ->
  zr_width_covers lens root i op.
Proof.
  intros lens root i op Hz sym cw Hcf _.
  exfalso. exact (code_for_none_of_zero_counts lens sym cw Hz Hcf).
Qed.

(* ------------------------------------------------------------------ *)
(* Arm completion: from a classification WITHOUT the negative          *)
(* conjuncts (what q4's keystone walk actually produces), derive the   *)
(* full frozen trichotomy.  Every negative is filled by a lemma above: *)
(* width from children, no_short/no_long from the max==1 population,   *)
(* the vacuity family at the accepted-EMPTY table.  Population facts   *)
(* ride INSIDE the marker disjuncts (a complete table has live high    *)
(* counts, so they cannot be lemma-global premises).                   *)

Definition zr_two_own_v3 (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) : Prop :=
  forall i, 0 <= i < 2 ^ root ->
    (exists sym cw, code_for lens 15%nat sym = Some cw
       /\ Z.of_nat (length cw) <= root
       /\ T i = ent sym
       /\ c_bits (ent sym) = Z.of_nat (length cw)
       /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw)
    \/ (c_bits (T i) = root
        /\ 1 <= c_op (T i) <= 15 - root
        /\ 2 ^ root <= c_val (T i)
        /\ zr_width_covers lens root i (c_op (T i))
        /\ zr_ptr_children T root lens ent i (c_op (T i)) (c_val (T i)))
    \/ (T i = mkCodeT 64 1 0
        /\ root = 1
        /\ zr_no_short_code lens root i
        /\ zr_no_long_code_at lens root i).

(** The classification a positive ownership walk yields per root cell:
    leaf arm verbatim; pointer arm with geometry + children only; the
    marker arm replaced by WHERE the marker is and WHAT the population
    is (max==1 incomplete: marker at cell 1, exactly one 1-bit code, no
    longer codes; accepted-EMPTY: any cell, no codes at all). *)
Lemma two_own_v3_of_parts :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code),
    0 <= root ->
    (forall s1 s2 cw1 cw2,
        code_for lens 15%nat s1 = Some cw1 ->
        code_for lens 15%nat s2 = Some cw2 ->
        s1 <> s2 ->
        is_prefix cw1 cw2 = false) ->
    (forall i, 0 <= i < 2 ^ root ->
        (exists sym cw, code_for lens 15%nat sym = Some cw
           /\ Z.of_nat (length cw) <= root
           /\ T i = ent sym
           /\ c_bits (ent sym) = Z.of_nat (length cw)
           /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw)
        \/ (c_bits (T i) = root
            /\ 1 <= c_op (T i) <= 15 - root
            /\ 2 ^ root <= c_val (T i)
            /\ zr_ptr_children T root lens ent i (c_op (T i)) (c_val (T i)))
        \/ (T i = mkCodeT 64 1 0 /\ root = 1 /\ i = 1
            /\ count_len lens 1%nat = 1%nat
            /\ (forall l : nat, (2 <= l <= 15)%nat ->
                  count_len lens l = 0%nat))
        \/ (T i = mkCodeT 64 1 0 /\ root = 1
            /\ (forall l : nat, (1 <= l <= 15)%nat ->
                  count_len lens l = 0%nat))) ->
    zr_two_own_v3 T root lens ent.
Proof.
  intros T root lens ent Hroot Hpf Hcls i Hi.
  destruct (Hcls i Hi) as [Hleaf | [Hptr | [Hm1 | Hm0]]].
  - left. exact Hleaf.
  - right; left.
    destruct Hptr as (Hb & Hop & Hval & Hch).
    refine (conj Hb (conj Hop (conj Hval (conj _ Hch)))).
    exact (width_covers_of_children T root lens ent i (c_op (T i))
             (c_val (T i)) Hroot ltac:(lia) Hpf Hch).
  - right; right.
    destruct Hm1 as (Hrec & Hr1 & Hi1 & Hc1 & Hh2).
    subst root i.
    exact (conj Hrec (conj eq_refl
             (conj (no_short_code_max1 lens Hc1)
                   (no_long_code_max1 lens 1 Hh2)))).
  - right; right.
    destruct Hm0 as (Hrec & Hr1 & Hz).
    exact (conj Hrec (conj Hr1
             (conj (no_short_code_none lens root i Hz)
                   (no_long_code_none lens root i Hz)))).
Qed.
