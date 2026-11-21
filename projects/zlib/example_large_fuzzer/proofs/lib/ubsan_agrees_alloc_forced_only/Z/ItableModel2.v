(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fill_iter (here hs next incr : Z) (j : nat) (tbl : arr) : arr :=
  match j with
  | O => tbl
  | S j' => fill_iter here hs next incr j' (arr_set tbl (next + (hs + Z.of_nat j' * incr)) here)
  end.

Definition fill_step (here incr huff drop next : Z) (ft : Z * arr) : bool * (Z * arr) :=
  let '(fill, tbl) := ft in
  let fill := wrap32 (fill - incr) in
  let tbl := arr_set tbl (next + (Z.shiftr huff drop + fill)) here in
  if negb (fill =? 0) then (true, (fill, tbl)) else (false, (fill, tbl)).

Lemma it_fill_eq : forall here incr huff drop next fill tbl,
  it_fill here incr huff drop next fill tbl = snd (loopZ fill (fill_step here incr huff drop next) (fill, tbl)).
Proof. reflexivity. Qed.

Lemma fill_loopZ : forall here incr huff drop next j n tbl,
  (1 <= j)%nat -> Z.of_nat j <= n -> 0 < incr -> Z.of_nat j * incr < 2 ^ 32 ->
  loopZ n (fill_step here incr huff drop next) (Z.of_nat j * incr, tbl)
  = (0, fill_iter here (Z.shiftr huff drop) next incr j tbl).
Proof.
  intros here incr huff drop next j. induction j as [|j IH]; intros n tbl Hj Hn Hi Hb; [lia|].
  rewrite loopZ_step by lia. unfold fill_step at 1.
  assert (Hw : wrap32 (Z.of_nat (S j) * incr - incr) = Z.of_nat j * incr).
  { replace (Z.of_nat (S j) * incr - incr) with (Z.of_nat j * incr) by lia. apply wrap32_id. nia. }
  rewrite Hw. cbn [fill_iter].
  destruct j as [|j'].
  - cbn [Z.of_nat Z.mul Z.eqb negb]. rewrite Z.add_0_r. reflexivity.
  - replace (Z.of_nat (S j') * incr =? 0) with false by (symmetry; apply Z.eqb_neq; nia). cbn [negb].
    rewrite IH by (try lia; nia). reflexivity.
Qed.

Lemma it_fill_spec : forall here incr huff drop next j tbl,
  (1 <= j)%nat -> 0 < incr -> Z.of_nat j * incr < 2 ^ 32 ->
  it_fill here incr huff drop next (Z.of_nat j * incr) tbl = fill_iter here (Z.shiftr huff drop) next incr j tbl.
Proof.
  intros here incr huff drop next j tbl Hj Hi Hb. rewrite it_fill_eq, fill_loopZ; try assumption; [reflexivity|nia].
Qed.

Lemma fill_iter_len : forall here hs next incr j tbl, arr_len (fill_iter here hs next incr j tbl) = arr_len tbl.
Proof.
  intros here hs next incr j. induction j as [|j IH]; intros tbl; [reflexivity|].
  cbn [fill_iter]. rewrite IH. apply arr_len_set.
Qed.

(* [comment removed for export] *)
Lemma fill_iter_S : forall here hs next incr j tbl,
  fill_iter here hs next incr (S j) tbl = fill_iter here hs next incr j (arr_set tbl (next + (hs + Z.of_nat j * incr)) here).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint incr_rec (huff : Z) (n : nat) (c : Z) : Z :=
  match n with
  | O => c
  | S n' => if negb (Z.land huff c =? 0) then incr_rec huff n' (Z.shiftr c 1) else c
  end.

Lemma loopZ_incr : forall huff n c,
  loopZ (Z.of_nat n) (fun incr => if negb (Z.land huff incr =? 0) then (true, Z.shiftr incr 1) else (false, incr)) c
  = incr_rec huff n c.
Proof.
  intros huff n. induction n as [|n IH]; intros c.
  - cbn [incr_rec]. apply loopZ_le0. lia.
  - rewrite loopZ_step by lia. cbn [incr_rec].
    destruct (negb (Z.land huff c =? 0)); [|reflexivity].
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia. apply IH.
Qed.

Lemma it_incr_back_rec : forall huff len, it_incr_back huff len = incr_rec huff 32 (shl32 1 (len - 1)).
Proof. intros. unfold it_incr_back. apply (loopZ_incr huff 32). Qed.

(* [comment removed for export] *)

Lemma incr_rec_range : forall huff n c, 0 <= c -> 0 <= incr_rec huff n c <= c.
Proof.
  intros huff n. induction n as [|n IH]; intros c Hc; cbn [incr_rec]; [lia|].
  destruct (negb _); [|lia].
  assert (0 <= Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  specialize (IH (Z.shiftr c 1) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition curr_step (count : arr) (drop max : Z) (cl : Z * Z) : bool * (Z * Z) :=
  let '(curr, lft) := cl in
  if wrap32 (curr + drop) <? max then
    let lft := lft - arr_get count (wrap32 (curr + drop)) in
    if lft <=? 0 then (false, (curr, lft))
    else (true, (wrap32 (curr + 1), Z.shiftl lft 1))
  else (false, (curr, lft)).

Fixpoint curr_rec (count : arr) (drop max : Z) (n : nat) (curr lft : Z) : Z * Z :=
  match n with
  | O => (curr, lft)
  | S n' => let '(c, cl) := curr_step count drop max (curr, lft) in
            if c then curr_rec count drop max n' (fst cl) (snd cl) else cl
  end.

Lemma loopZ_curr : forall count drop max n curr lft,
  loopZ (Z.of_nat n) (curr_step count drop max) (curr, lft) = curr_rec count drop max n curr lft.
Proof.
  intros count drop max n. induction n as [|n IH]; intros curr lft.
  - cbn [curr_rec]. apply loopZ_le0. lia.
  - rewrite loopZ_step by lia. cbn [curr_rec].
    destruct (curr_step count drop max (curr, lft)) as [c [c1 l1]]. destruct c; [|reflexivity].
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia. apply IH.
Qed.

Lemma it_subtable_curr_rec : forall count len drop max,
  it_subtable_curr count len drop max =
  fst (curr_rec count drop max 16 (wrap32 (len - drop)) (swrap32 (Z.shiftl 1 (wrap32 (len - drop))))).
Proof. intros. unfold it_subtable_curr. cbv zeta. f_equal. apply (loopZ_curr count drop max 16). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TripOk.
Variable x : ItCtx.
Variable WN : Z.
Variable LN : Z.
Variable TN : Z.
Variable st : ItSt.
Hypothesis Hok : it_trip_ok x WN LN TN st = true.

Local Ltac peel H :=
  repeat (apply andb_prop in H; destruct H as [H ?]).

Lemma trip_ok_basic :
  0 <= t_sym st < WN /\ 1 <= t_len st <= 15 /\ 0 <= t_drop st <= t_len st
  /\ t_len st - t_drop st <= t_curr st <= 15 /\ 0 <= t_huff st < 65536
  /\ 0 <= t_next st /\ 0 <= t_used st < 65536 /\ 0 <= t_min st < 65536.
Proof.
  unfold it_trip_ok in Hok. cbv zeta in Hok.
  repeat match goal with
         | H : (?a && ?b) = true |- _ => apply andb_prop in H; destruct H
         end.
  repeat match goal with
         | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
         | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
         end.
  lia.
Qed.

Lemma trip_ok_work :
  let w := arr_get (t_work st) (t_sym st) in
  0 <= w < 65536 /\
  (w + 1 <? it_match (x_ty x) = false -> it_match (x_ty x) <=? w = true -> 0 <= w - it_match (x_ty x) < it_ext_len (x_ty x) WN).
Proof.
  unfold it_trip_ok in Hok. cbv zeta in Hok.
  repeat match goal with
         | H : (?a && ?b) = true |- _ => apply andb_prop in H; destruct H
         end.
  cbv zeta. split.
  - repeat match goal with
           | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
           | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
           end. lia.
  - intros E1 E2.
    match goal with H : (if arr_get (t_work st) (t_sym st) + 1 <? _ then _ else _) = true |- _ =>
      rewrite E1, E2 in H; apply Z.ltb_lt in H end.
    apply Z.leb_le in E2. lia.
Qed.

Lemma trip_ok_fill :
  t_next st + Z.shiftr (t_huff st) (t_drop st) + Z.shiftl 1 (t_curr st) - Z.shiftl 1 (t_len st - t_drop st) < TN.
Proof.
  unfold it_trip_ok in Hok. cbv zeta in Hok.
  repeat match goal with
         | H : (?a && ?b) = true |- _ => apply andb_prop in H; destruct H
         end.
  match goal with H : (t_next st + _ + _ - _ <? TN) = true |- _ => apply Z.ltb_lt in H; exact H end.
Qed.

Lemma trip_ok_next :
  let c := wrap16 (arr_get (t_count st) (t_len st) - 1) in
  c = 0 -> t_len st <> x_max x ->
  let w' := arr_get (t_work st) (t_sym st + 1) in
  t_sym st + 1 < WN /\ 0 <= w' /\ 0 <= x_lens_ofs x + w' < LN
  /\ 1 <= arr_get (x_lens x) (x_lens_ofs x + w') <= 15.
Proof.
  unfold it_trip_ok in Hok. cbv zeta in Hok.
  repeat match goal with
         | H : (?a && ?b) = true |- _ => apply andb_prop in H; destruct H
         end.
  cbv zeta. intros Hc Hm.
  match goal with H : (if (wrap16 _ =? 0) && negb _ then _ else true) = true |- _ =>
    rewrite Hc in H; cbn [Z.eqb] in H;
    replace (negb (t_len st =? x_max x)) with true in H by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; exact Hm);
    cbn [andb] in H;
    repeat (apply andb_prop in H; destruct H as [H ?])
  end.
  repeat match goal with
         | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
         | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
         end. lia.
Qed.

Lemma trip_ok_sub : forall st',
  it_step x st = ItCont st' ->
  (t_low st' <> t_low st \/ t_next st' <> t_next st) ->
  0 <= x_table x + t_low st' < TN /\ 1 <= t_curr st' <= 15 /\ t_next st <= t_next st'.
Proof.
  intros st' Hs Hne.
  unfold it_trip_ok in Hok. cbv zeta in Hok.
  repeat match goal with
         | H : (?a && ?b) = true |- _ => apply andb_prop in H; destruct H
         end.
  match goal with H : match it_step x st with _ => _ end = true |- _ =>
    rewrite Hs in H;
    replace (negb (t_low st' =? t_low st) || negb (t_next st' =? t_next st)) with true in H
      by (symmetry; apply Bool.orb_true_iff; destruct Hne as [Hne|Hne];
          [left|right]; apply Bool.negb_true_iff, Z.eqb_neq; exact Hne);
    repeat (apply andb_prop in H; destruct H as [H ?])
  end.
  repeat match goal with
         | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
         | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
         end. lia.
Qed.
End TripOk.
