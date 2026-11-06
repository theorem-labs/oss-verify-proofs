From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Local Open Scope nat_scope.

(* The reader's allocation charge.  chg_ev e counts the input bytes that pay for the event e, and the bytes that pay
   for the events of one parse are disjoint:
   - a string token (value or member name) of q raw chars before its closing quote: EAlloc (S q), charge max q 1,
     paid by those q chars, or, when q = 0, by a value's closing quote or a name's ':' (a value string consumes q + 2
     bytes, a name q + 3);
   - a number of k >= 1 bytes: EAlloc (S k), charge k, paid by its k bytes;
   - the kids array of a container grown to 8 (EGrow 0 448), charge 2: paid by the container's opener and closer;
     grown to 16 (EGrow 448 896), charge 8: paid by the commas 1 .. 8; grown from cap >= 16 to 2 cap, charge cap / 2:
     paid by the commas cap/2 + 1 .. cap;
   - the keys array of an object grown to 8 (EGrow 0 64), charge 2: paid by the first member name's two quotes; grown
     to 16, charge 8: paid by the quotes of the names 2 .. 8; grown from cap >= 16 to 2 cap, charge cap / 2: paid by
     the quotes of the names cap/2 + 1 .. cap (2 per name);
   - an unclosed container of a refused parse owes at most 3 (its closer and its first name's quotes), and at most
     MAXD containers are open.
   So the charge of a parse is at most length x + 3 * MAXD, and at most length x when the parse succeeds
   (jr_run_charge, jr_run_charge_ok).  With the grow sizes fixed by ev_shape (jr_run_shape), cnt_by_charge turns the
   charge bound into a count bound for the events whose request satisfies any predicate P; cntG / cntS count the grow
   events and the other events apart (jr_run_cntG, jr_run_cntS), and the grow events of an accepted parse are those
   of its tree's ttrace (jr_run_grows_tree). *)

Definition chg_ev (e : ev) : nat :=
  match e with
  | EAlloc n => Nat.max (n - 1) 1
  | EGrow _ n => if Nat.eqb (n mod 7) 0
                 then (if Nat.eqb n 448 then 2 else if Nat.eqb n 896 then 8 else n / 224)
                 else (if Nat.eqb n 64 then 2 else if Nat.eqb n 128 then 8 else n / 32)
  | EFail _ | EFree _ => 0
  end.

Fixpoint chg (t : list ev) : nat := match t with [] => 0 | e :: r => chg_ev e + chg r end.

(* gchg c: the charge of the grow of one array (kids or keys) to capacity c; K cap: the charge of all its grows up to
   capacity cap. *)
Definition gchg (c : nat) : nat := if Nat.eqb c 8 then 2 else if Nat.eqb c 16 then 8 else c / 4.

Definition K (cap : nat) : nat := if Nat.eqb cap 0 then 0 else if Nat.eqb cap 8 then 2 else cap / 2 + 2.

Definition capok (cap : nat) : Prop := cap = 0%nat \/ exists j, cap = (8 * 2 ^ j)%nat.

Definition ev_shape (e : ev) : Prop :=
  match e with
  | EGrow _ n => exists j, (n = 448 * 2 ^ j \/ n = 64 * 2 ^ j)%nat
  | _ => True
  end.

Definition req_ev (e : ev) : option nat :=
  match e with
  | EAlloc n | EGrow _ n => Some (n + 16)%nat
  | _ => None
  end.

Fixpoint cntR (P : nat -> bool) (t : list ev) : nat :=
  match t with
  | [] => 0
  | e :: r =>
    match req_ev e with
    | Some q => if P q then S (cntR P r) else cntR P r
    | None => cntR P r
    end
  end.

(* The grow events and the other events, counted apart. *)
Definition is_grow (e : ev) : bool := match e with EGrow _ _ => true | _ => false end.
Definition cntG (P : nat -> bool) (t : list ev) : nat := cntR P (filter is_grow t).
Definition cntS (P : nat -> bool) (t : list ev) : nat := cntR P (filter (fun e => negb (is_grow e)) t).

Lemma cntR_split : forall P t, cntR P t = cntG P t + cntS P t.
Proof.
  intros P t. unfold cntG, cntS. induction t as [|e r IH]; [reflexivity|].
  destruct e as [n|m n|n|n]; cbn [filter is_grow negb cntR req_ev];
    repeat match goal with |- context [P ?q] => destruct (P q) end; lia.
Qed.

Lemma chg_filter_le : forall f t, chg (filter f t) <= chg t.
Proof.
  intros f t. induction t as [|e r IH]; cbn [filter chg]; [lia|]. destruct (f e); cbn [chg]; lia.
Qed.

(* The count bound: if every event whose request satisfies P charges at least m, then m times their number is at most
   the charge of the trace. *)

Lemma cnt_by_charge_in : forall (P : nat -> bool) m t,
  Forall (fun e => match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end) t ->
  (m * cntR P t <= chg t)%nat.
Proof.
  intros P m t Ht. induction Ht as [|e t He Ht IH]; cbn [cntR chg]; [lia|]. cbv beta in He.
  destruct (req_ev e) as [q|]; [|lia].
  destruct (P q); [|lia].
  specialize (He eq_refl). rewrite Nat.mul_succ_r. lia.
Qed.

Theorem cnt_by_charge : forall (P : nat -> bool) m t, Forall ev_shape t ->
  (forall e, ev_shape e -> match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end) ->
  (m * cntR P t <= chg t)%nat.
Proof. intros P m t Ht H. apply cnt_by_charge_in. eapply Forall_impl; [|exact Ht]. exact H. Qed.

(* The boolean check form of the per-event minimum, for a predicate P whose requests lie in lo .. hi.  An EAlloc n
   charges max (n - 1) 1 = max ((n + 16) - 17) 1, which grows with the request, so max (lo - 17) 1 is its least charge
   (chk_minS); the grows of ev_shape are checked one by one for j <= J, and hi < 64 * 2 ^ (S J) + 16 puts every larger
   grow outside P (chk_minG). *)

Definition chk_minS (m lo : nat) : bool := Nat.leb m (Nat.max (lo - 17) 1).

Definition chk_minG (P : nat -> bool) (m hi J : nat) : bool :=
  forallb (fun j =>
    implb (P (448 * 2 ^ j + 16)) (Nat.leb m (chg_ev (EGrow 0 (448 * 2 ^ j)))) &&
    implb (P (64 * 2 ^ j + 16)) (Nat.leb m (chg_ev (EGrow 0 (64 * 2 ^ j))))) (seq 0 (S J)) &&
  Nat.ltb hi (64 * 2 ^ (S J) + 16).

Definition chk_min (P : nat -> bool) (m lo hi J : nat) : bool := chk_minS m lo && chk_minG P m hi J.

Lemma chk_minS_ok : forall P m lo, chk_minS m lo = true -> (forall r, P r = true -> (lo <= r)%nat) ->
  forall e, ev_shape e -> is_grow e = false ->
  match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end.
Proof.
  intros P m lo H HR e _ Hg. unfold chk_minS in H. apply Nat.leb_le in H.
  destruct e as [n|m0 n|n|n]; cbn [is_grow] in Hg; try discriminate; cbn [req_ev]; try exact I.
  intros HP. pose proof (HR _ HP). cbn [chg_ev]. lia.
Qed.

Lemma chk_minG_ok : forall P m hi J, chk_minG P m hi J = true -> (forall r, P r = true -> (r <= hi)%nat) ->
  forall e, ev_shape e -> is_grow e = true ->
  match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end.
Proof.
  intros P m hi J H HR e He Hg. unfold chk_minG in H.
  apply andb_true_iff in H as [H2 H3]. apply Nat.ltb_lt in H3. rewrite forallb_forall in H2.
  destruct e as [n|m0 n|n|n]; cbn [is_grow] in Hg; try discriminate.
  cbn [req_ev]. intros HP. pose proof (HR _ HP) as Hhi.
  change (chg_ev (EGrow m0 n)) with (chg_ev (EGrow 0 n)).
  destruct He as (j & Hn).
  destruct (Nat.le_gt_cases j J) as [Hj|Hj].
  - assert (Hin : In j (seq 0 (S J))) by (apply in_seq; lia).
    specialize (H2 j Hin). cbv beta in H2. apply andb_true_iff in H2 as [Ha Hb].
    destruct Hn as [-> | ->].
    + rewrite HP in Ha. cbn [implb] in Ha. apply Nat.leb_le in Ha. exact Ha.
    + rewrite HP in Hb. cbn [implb] in Hb. apply Nat.leb_le in Hb. exact Hb.
  - exfalso. assert (Hp : 2 ^ S J <= 2 ^ j) by (apply Nat.pow_le_mono_r; lia).
    set (p := 2 ^ j) in *. set (q := 2 ^ S J) in *. clearbody p q.
    destruct Hn as [-> | ->]; lia.
Qed.

Theorem chk_min_ok : forall P m lo hi J, chk_min P m lo hi J = true ->
  (forall r, P r = true -> (lo <= r <= hi)%nat) ->
  forall e, ev_shape e -> match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end.
Proof.
  intros P m lo hi J H HR e He. unfold chk_min in H. apply andb_true_iff in H as [HS HG].
  destruct (is_grow e) eqn:Eg.
  - exact (chk_minG_ok P m hi J HG (fun r Hr => proj2 (HR r Hr)) e He Eg).
  - exact (chk_minS_ok P m lo HS (fun r Hr => proj1 (HR r Hr)) e He Eg).
Qed.

Corollary cnt_by_chk : forall P m lo hi J t, chk_min P m lo hi J = true ->
  (forall r, P r = true -> (lo <= r <= hi)%nat) -> Forall ev_shape t -> (m * cntR P t <= chg t)%nat.
Proof. intros P m lo hi J t H HR Ht. apply cnt_by_charge; [exact Ht|]. exact (chk_min_ok P m lo hi J H HR). Qed.

(* Arithmetic of the grow charges.  lia does not reason about Nat.div and Nat.modulo; dm replaces each a / b and
   a mod b by fresh variables bound by a = b * q + r and r < b.  eqbs splits on each Nat.eqb of the goal. *)

Ltac dm1 a b :=
  let q := fresh "q" in let r := fresh "r" in
  pose proof (Nat.div_mod_eq a b); pose proof (Nat.mod_upper_bound a b ltac:(discriminate));
  set (q := a / b) in *; set (r := a mod b) in *; clearbody q r.

Ltac dm := repeat match goal with
  | |- context [?a / ?b] => dm1 a b
  | |- context [?a mod ?b] => dm1 a b
  | H : context [?a / ?b] |- _ => dm1 a b
  | H : context [?a mod ?b] |- _ => dm1 a b
  end.

Ltac eqbs := repeat match goal with
  | |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); cbn beta iota
  end.

Lemma pow2_pos : forall j, 1 <= 2 ^ j.
Proof. induction j as [|j IH]; cbn [Nat.pow]; lia. Qed.

Lemma pow2_mod7 : forall j, 2 ^ j mod 7 = 1 \/ 2 ^ j mod 7 = 2 \/ 2 ^ j mod 7 = 4.
Proof.
  induction j as [|j IH]; [left; reflexivity|].
  cbn [Nat.pow]. set (p := 2 ^ j) in *. clearbody p. dm; lia.
Qed.

Lemma chg_kids : forall m c, chg_ev (EGrow m (56 * c)) = gchg c.
Proof. intros m c. unfold chg_ev, gchg. eqbs; dm; lia. Qed.

Lemma chg_keys : forall m c, capok c -> c <> 0 -> chg_ev (EGrow m (8 * c)) = gchg c.
Proof.
  intros m c [->|[j ->]] Hc; [contradiction|].
  pose proof (pow2_mod7 j). pose proof (pow2_pos j). set (p := 2 ^ j) in *. clearbody p.
  unfold chg_ev, gchg. eqbs; dm; lia.
Qed.

Lemma shape_kids : forall m c, capok c -> c <> 0 -> ev_shape (EGrow m (56 * c)).
Proof. intros m c [->|[j ->]] Hc; [contradiction|]. exists j. left. set (p := 2 ^ j). lia. Qed.

Lemma shape_keys : forall m c, capok c -> c <> 0 -> ev_shape (EGrow m (8 * c)).
Proof. intros m c [->|[j ->]] Hc; [contradiction|]. exists j. right. set (p := 2 ^ j). lia. Qed.

Definition ncap (cap : nat) : nat := if Nat.eqb cap 0 then 8 else 2 * cap.

Lemma ncap_pos : forall c, c <> 0 -> ncap c = 2 * c.
Proof. intros c H. unfold ncap. destruct (Nat.eqb c 0) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity]. Qed.

Lemma K_grow : forall cap, capok cap -> capok (ncap cap) /\ ncap cap <> 0 /\ K cap + gchg (ncap cap) = K (ncap cap).
Proof.
  intros cap [->|[j ->]].
  - split; [right; exists 0; reflexivity|]. split; [unfold ncap; cbn [Nat.eqb]; lia|]. reflexivity.
  - pose proof (pow2_pos j) as Hp.
    rewrite ncap_pos by lia.
    split; [right; exists (S j); cbn [Nat.pow]; set (p := 2 ^ j); lia|].
    set (p := 2 ^ j) in *. clearbody p. unfold K, gchg. eqbs; dm; lia.
Qed.

Lemma K_le : forall n cap, capok cap -> (cap <= Nat.max 8 (2 * n))%nat -> (K cap <= n + 2)%nat.
Proof.
  intros n cap [->|[j ->]] H; [change (K 0) with 0; lia|].
  pose proof (pow2_pos j). set (p := 2 ^ j) in *. clearbody p. unfold K. eqbs; dm; lia.
Qed.

(* Traces. *)

Lemma chg_app : forall a b, chg (a ++ b) = chg a + chg b.
Proof. induction a as [|e r IH]; intros b; cbn [chg app]; [reflexivity|]. rewrite IH. lia. Qed.

Ltac shp := repeat match goal with
  | H : Forall ev_shape ?t |- Forall ev_shape ?t => exact H
  | |- Forall ev_shape (_ ++ _) => apply Forall_app; split
  | |- Forall ev_shape [] => apply Forall_nil
  | |- Forall ev_shape (EGrow _ (56 * _) :: _) => apply Forall_cons; [apply shape_kids; assumption|]
  | |- Forall ev_shape (EGrow _ (8 * _) :: _) => apply Forall_cons; [apply shape_keys; assumption|]
  | |- Forall ev_shape (_ :: _) => apply Forall_cons; [exact I|]
  end.

(* pspec e L B res: the trace's events have their shapes, its charge is at most B, and a result Some (v, r) leaves
   at least e bytes of L unpaid besides r. *)
Definition pspec {A : Type} (e L B : nat) (res : option (A * list Z) * list ev * list bool) : Prop :=
  Forall ev_shape (snd (fst res)) /\ (chg (snd (fst res)) <= B)%nat /\
  (forall v r, fst (fst res) = Some (v, r) -> (chg (snd (fst res)) + length r + e <= L)%nat).

Lemma pspec_refuse : forall A e L B ok, @pspec A e L B (None, [], ok).
Proof.
  intros A e L B ok. unfold pspec. cbn [fst snd chg]. split; [constructor|]. split; [lia|].
  intros v r H. discriminate.
Qed.

Lemma pspec_weak : forall A e L B e' L' B' (res : option (A * list Z) * list ev * list bool),
  pspec e L B res -> (B <= B')%nat -> (L + e' <= L' + e)%nat -> pspec e' L' B' res.
Proof.
  intros A e L B e' L' B' res (H1 & H2 & H3) HB HL. split; [exact H1|]. split; [lia|].
  intros v r Hr. specialize (H3 v r Hr). lia.
Qed.

(* The list level: jrl at depth d with n items read into arrays of capacity cap.  The 1 is the opener the caller
   consumed, n the commas read, 2 n the names' quotes read; 3 + 3 * (MAXD - d) is the debt of the open containers. *)
Definition cl (o : bool) (n cap : nat) (y : list Z) (d : nat) (res : option (jv * list Z) * list ev * list bool)
  : Prop :=
  Forall ev_shape (snd (fst res)) /\
  (chg (snd (fst res)) + (1 + Nat.b2n o) * K cap <=
     length y + 1 + n + Nat.b2n o * (2 * n) + 3 + 3 * (MAXD - d))%nat /\
  (forall v r, fst (fst res) = Some (v, r) ->
     (chg (snd (fst res)) + (1 + Nat.b2n o) * K cap + length r <= length y + 1 + n + Nat.b2n o * (2 * n))%nat).

Lemma jrealloc_cases : forall m n ok,
  jrealloc m n ok = (Some tt, [EGrow m n], tl ok) \/ jrealloc m n ok = (None, [EFail n], tl ok).
Proof. intros m n [|[|] ok]; unfold jrealloc, take; cbv beta iota zeta; [left|left|right]; reflexivity. Qed.

Lemma grow_chg : forall o n cap ok, inv n cap -> capok cap ->
  match grow o n cap ok with
  | (Some cap1, t, _) => Forall ev_shape t /\ capok cap1 /\
      chg t + (1 + Nat.b2n o) * K cap = (1 + Nat.b2n o) * K cap1
  | (None, t, _) => Forall ev_shape t /\ chg t + (1 + Nat.b2n o) * K cap <= (1 + Nat.b2n o) * (n + 2)
  end.
Proof.
  intros o n cap ok Hi Hc. unfold grow.
  destruct (Nat.ltb n cap) eqn:E.
  - unfold jret. cbn [chg]. split; [constructor|]. split; [exact Hc|]. lia.
  - apply Nat.ltb_ge in E. destruct Hi as (Hi1 & Hi2 & Hi3 & Hi4).
    assert (n = cap) by lia. subst n.
    destruct (K_grow cap Hc) as (C1 & C2 & C3).
    cbv zeta. change (if Nat.eqb cap 0 then 8 else 2 * cap) with (ncap cap).
    assert (Hk : K (ncap cap) <= cap + 2).
    { apply K_le; [exact C1|]. unfold ncap. destruct (Nat.eqb cap 0); lia. }
    unfold jbind. cbv beta.
    destruct (jrealloc_cases (56 * cap) (56 * ncap cap) ok) as [E1|E1]; rewrite E1; cbv beta iota.
    + destruct o; cbv beta iota.
      * destruct (jrealloc_cases (8 * cap) (8 * ncap cap) (tl ok)) as [E2|E2]; rewrite E2; cbv beta iota.
        -- unfold jret. cbn [app chg Nat.b2n]. rewrite chg_kids, (chg_keys _ _ C1 C2).
           split; [shp|]. split; [exact C1|]. lia.
        -- cbn [app chg Nat.b2n]. rewrite chg_kids. cbn [chg_ev]. split; [shp|]. lia.
      * unfold jret. cbn [app chg Nat.b2n]. rewrite chg_kids. split; [shp|]. split; [exact C1|]. lia.
    + cbn [chg chg_ev]. split; [shp|]. destruct o; cbn [Nat.b2n]; lia.
Qed.

Lemma str_chg : forall z ok, pspec 0 (length z) (length z) (jr_string z ok).
Proof.
  intros z ok. unfold jr_string.
  destruct (scan z) as [q|] eqn:Es; cbv beta iota; [|apply pspec_refuse].
  pose proof (scan_quote z q Es) as [Hq _].
  unfold jbind, jalloc, take.
  destruct ok as [|b ok]; [|destruct b]; cbv beta iota.
  - destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota.
    + destruct (decode_stop z s r Ed) as (q' & Es' & Hr & _). rewrite Es in Es'. injection Es' as <-.
      unfold jret, pspec. cbn [fst snd app chg chg_ev]. split; [shp|]. split; [lia|].
      intros s' r' E. injection E as _ <-. rewrite Hr, length_skipn. lia.
    + unfold jfree, jrefuse, pspec. cbn [fst snd app chg chg_ev]. split; [shp|]. split; [lia|].
      intros s' r' E. discriminate.
  - destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota.
    + destruct (decode_stop z s r Ed) as (q' & Es' & Hr & _). rewrite Es in Es'. injection Es' as <-.
      unfold jret, pspec. cbn [fst snd app chg chg_ev]. split; [shp|]. split; [lia|].
      intros s' r' E. injection E as _ <-. rewrite Hr, length_skipn. lia.
    + unfold jfree, jrefuse, pspec. cbn [fst snd app chg chg_ev]. split; [shp|]. split; [lia|].
      intros s' r' E. discriminate.
  - unfold pspec. cbn [fst snd chg chg_ev]. split; [shp|]. split; [lia|]. intros s' r' E. discriminate.
Qed.

Lemma name_chg : forall o y ok, pspec (2 * Nat.b2n o) (length y) (length y) (jr_name o y ok).
Proof.
  intros o y ok. destruct o.
  2: { unfold jr_name, jret, pspec. cbn [fst snd chg Nat.b2n]. split; [constructor|]. split; [lia|].
       intros nm y1 E. injection E as _ <-. lia. }
  unfold jr_name. cbv beta iota.
  destruct (skip y) as [|b z] eqn:Ey; cbv beta iota; [apply pspec_refuse|].
  assert (Hy : length (b :: z) <= length y) by (rewrite <- Ey; apply skip_len). cbn [length] in Hy.
  destruct (b =? 34)%Z; cbv beta iota; [|apply pspec_refuse].
  unfold jbind at 1. cbv beta.
  pose proof (str_chg z ok) as Hs. unfold pspec in Hs.
  destruct (jr_string z ok) as [[[[nm r]|] t] ok1]; cbn [fst snd] in Hs; destruct Hs as (S1 & S2 & S3);
    cbv beta iota.
  - specialize (S3 nm r eq_refl).
    destruct (skip r) as [|c r1] eqn:Er; cbv beta iota.
    + unfold jbind, jfree, jrefuse, pspec. cbn [fst snd app]. rewrite chg_app. cbn [chg chg_ev].
      split; [shp|]. split; [lia|]. intros nm' y1 E. discriminate.
    + assert (Hr : length (c :: r1) <= length r) by (rewrite <- Er; apply skip_len). cbn [length] in Hr.
      destruct (c =? 58)%Z; cbv beta iota.
      * unfold jret, pspec. cbn [fst snd Nat.b2n]. rewrite app_nil_r.
        split; [exact S1|]. split; [lia|]. intros nm' y1 E. injection E as _ <-. lia.
      * unfold jbind, jfree, jrefuse, pspec. cbn [fst snd app]. rewrite chg_app. cbn [chg chg_ev].
        split; [shp|]. split; [lia|]. intros nm' y1 E. discriminate.
  - unfold pspec. cbn [fst snd]. split; [exact S1|]. split; [lia|]. intros nm' y1 E. discriminate.
Qed.

Lemma lit_chg : forall w v x ok, w <> [] -> pspec 0 (length x) (length x) (lit w v x ok).
Proof.
  intros w v x ok Hw. pose proof (lit_spec w v x ok Hw) as H.
  destruct (lit w v x ok) as [[[[u r]|] t] ok'].
  - destruct H as [-> Hr]. unfold pspec. cbn [fst snd chg]. split; [constructor|]. split; [lia|].
    intros v' r' E. injection E as _ <-. lia.
  - subst t. apply pspec_refuse.
Qed.

Lemma cont_chg : forall loop d o b y ok,
  (forall o' n cap acc y' ok', inv n cap -> capok cap -> cl o' n cap y' (S d) (loop (S d) o' n cap acc y' ok')) ->
  pspec 0 (length (b :: y)) (length (b :: y) + 3 * (MAXD - d)) (jr_cont loop d o (b :: y) ok).
Proof.
  intros loop d o b y ok HL. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; cbv beta iota; [apply pspec_refuse|].
  apply Nat.ltb_ge in Ed. cbn [tl]. cbv zeta.
  assert (Hloop : pspec 0 (length (b :: y)) (length (b :: y) + 3 * (MAXD - d)) (loop (S d) o 0 0 [] (skip y) ok)).
  { assert (Hi : inv 0 0) by (unfold inv; lia).
    assert (Hc : capok 0) by (left; reflexivity).
    pose proof (skip_len y) as Hy.
    destruct (HL o 0 0 [] (skip y) ok Hi Hc) as (A & B & C).
    change (K 0) with 0 in B, C.
    unfold pspec. cbn [length]. split; [exact A|]. split; [lia|].
    intros v r Hr. specialize (C v r Hr). lia. }
  destruct (skip y) as [|c r] eqn:Ey; cbv beta iota; [exact Hloop|].
  assert (Hy : length (c :: r) <= length y) by (rewrite <- Ey; apply skip_len). cbn [length] in Hy.
  destruct (c =? closer o)%Z; cbv beta iota; [|exact Hloop].
  unfold jret, pspec. cbn [fst snd chg length]. split; [constructor|]. split; [lia|].
  intros v r' Hr. injection Hr as _ <-. lia.
Qed.

(* The grow events of a trace, against PjRoundTrip.ttrace: tgo o n cap L is the trace of the items L read from n
   items into arrays of capacity cap. *)

Lemma fg_app : forall a b, filter is_grow (a ++ b) = filter is_grow a ++ filter is_grow b.
Proof.
  induction a as [|e r IH]; intros b; [reflexivity|]. cbn [app filter].
  destruct (is_grow e); [cbn [app]; rewrite IH; reflexivity|exact (IH b)].
Qed.

Definition tgo (o : bool) (n cap : nat) (L : list (list Z * jv)) : list ev :=
  if o then tgo_obj n cap L else tgo_arr n cap (map snd L).

Lemma tgo_nil : forall o n cap, tgo o n cap [] = [].
Proof. intros [|] n cap; reflexivity. Qed.

Lemma tgo_mk : forall o L, ttrace (mk o L) = tgo o 0 0 L.
Proof. intros [|] L; cbn [mk tgo]; [apply tt_obj|apply tt_arr]. Qed.

Lemma tgo_cons : forall o n cap nm v L,
  filter is_grow (tgo o n cap ((nm, v) :: L)) =
  filter is_grow (grow_ev o n cap) ++ filter is_grow (ttrace v) ++ filter is_grow (tgo o (S n) (gcap n cap) L).
Proof.
  intros [|] n cap nm v L; cbn [tgo tgo_obj tgo_arr map snd]; rewrite !fg_app; cbn [filter is_grow];
    rewrite ?fg_app; reflexivity.
Qed.

Lemma grow_some : forall o n cap ok cap1 tg ok1, grow o n cap ok = (Some cap1, tg, ok1) ->
  cap1 = gcap n cap /\ tg = grow_ev o n cap.
Proof.
  intros o n cap ok cap1 tg ok1 H.
  destruct (agrees_some _ _ _ _ _ _ (agrees_grow o n cap) H) as [E _].
  rewrite grow_all in E. injection E as E1 E2. split; symmetry; assumption.
Qed.

Lemma lit_grows : forall w u x ok v r tr ok', lit w u x ok = (Some (v, r), tr, ok') -> tr = [] /\ v = u.
Proof.
  intros w u x ok v r tr ok' H. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H; intros; subst. split; reflexivity.
Qed.

Section C.

Variable sm : list Z -> Z * Z.

Lemma num_chg : forall x ok, x <> [] -> pspec 0 (length x) (length x) (jr_number sm x ok).
Proof.
  intros x ok Hx. unfold jr_number. cbv beta zeta.
  set (j := match x with b :: _ => if (b =? 45)%Z then 1 else 0 | [] => 0 end).
  assert (Hj : j <= length x).
  { unfold j. destruct x as [|b x']; [contradiction|]. cbn [length]. destruct (b =? 45)%Z; lia. }
  clearbody j.
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c z] eqn:Ez; cbv beta iota; [apply pspec_refuse|].
  destruct (negb (digit c)); cbv beta iota; [apply pspec_refuse|].
  destruct ((c =? 48)%Z && match z with c1 :: _ => digit c1 | [] => false end)%bool; cbv beta iota;
    [apply pspec_refuse|].
  destruct (span numch z) as [a r] eqn:Es; cbv beta iota.
  pose proof (span_app _ _ _ _ Es) as Hz.
  assert (Ht : length (firstn j x ++ c :: a) + length r = length x).
  { rewrite length_app, length_firstn. cbn [length]. cbn [length] in Hsk.
    rewrite Hz, length_app in Hsk. lia. }
  assert (Ht1 : 1 <= length (firstn j x ++ c :: a)) by (rewrite length_app; cbn [length]; lia).
  set (txt := firstn j x ++ c :: a) in *. clearbody txt.
  unfold jbind, jalloc, take.
  destruct ok as [|b ok]; [|destruct b]; cbv beta iota.
  - destruct (whole sm txt); unfold jret, jrefuse, pspec; cbn [fst snd app chg chg_ev].
    + split; [shp|]. split; [lia|]. intros v r' E. injection E as _ <-. lia.
    + split; [shp|]. split; [lia|]. intros v r' E. discriminate.
  - destruct (whole sm txt); unfold jret, jrefuse, pspec; cbn [fst snd app chg chg_ev].
    + split; [shp|]. split; [lia|]. intros v r' E. injection E as _ <-. lia.
    + split; [shp|]. split; [lia|]. intros v r' E. discriminate.
  - unfold pspec. cbn [fst snd chg chg_ev]. split; [shp|]. split; [lia|]. intros v r' E. discriminate.
Qed.

Lemma chg_fuel : forall f,
  (forall d x ok, pspec 0 (length x) (length x + 3 * (MAXD - d)) (jrv sm f d x ok)) /\
  (forall d o n cap acc y ok, inv n cap -> capok cap -> cl o n cap y d (jrl sm f d o n cap acc y ok)).
Proof.
  induction f as [|f [IHv IHl]].
  - split.
    + intros d x ok. apply pspec_refuse.
    + intros d o n cap acc y ok Hi Hc. cbn [jrl]. unfold jrefuse, cl. cbn [fst snd chg].
      destruct Hi as (Hi1 & Hi2 & Hi3 & Hi4). pose proof (K_le n cap Hc Hi2) as HK.
      split; [constructor|]. destruct o; cbn [Nat.b2n]; (split; [lia|intros v r E; discriminate]).
  - split.
    + intros d x ok. cbn [jrv].
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota; [apply pspec_refuse|].
      assert (Hsx : length (b :: y) <= length x) by (rewrite <- Ex; apply skip_len).
      apply (pspec_weak _ 0 (length (b :: y)) (length (b :: y) + 3 * (MAXD - d))); [|lia|lia].
      destruct (b =? 123)%Z; cbv beta iota; [apply cont_chg; intros; apply IHl; assumption|].
      destruct (b =? 91)%Z; cbv beta iota; [apply cont_chg; intros; apply IHl; assumption|].
      destruct (b =? 34)%Z; cbv beta iota.
      * unfold jbind. cbv beta. pose proof (str_chg y ok) as Hs. unfold pspec in Hs.
        destruct (jr_string y ok) as [[[[s r]|] t] ok1]; cbn [fst snd] in Hs; destruct Hs as (S1 & S2 & S3);
          cbv beta iota.
        -- specialize (S3 s r eq_refl). unfold jret, pspec. cbn [fst snd]. rewrite app_nil_r.
           split; [exact S1|]. split; [cbn [length]; lia|].
           intros v r' Hr. injection Hr as _ <-. cbn [length]. lia.
        -- unfold pspec. cbn [fst snd]. split; [exact S1|]. split; [cbn [length]; lia|].
           intros v r' Hr. discriminate.
      * destruct (b =? 116)%Z; cbv beta iota.
        { eapply pspec_weak; [apply lit_chg; discriminate|lia|lia]. }
        destruct (b =? 102)%Z; cbv beta iota.
        { eapply pspec_weak; [apply lit_chg; discriminate|lia|lia]. }
        destruct (b =? 110)%Z; cbv beta iota.
        { eapply pspec_weak; [apply lit_chg; discriminate|lia|lia]. }
        eapply pspec_weak; [apply num_chg; discriminate|lia|lia].
    + intros d o n cap acc y ok Hi Hc. cbn [jrl]. unfold jbind at 1. cbv beta.
      pose proof (grow_chg o n cap ok Hi Hc) as Hg.
      pose proof (grow_spec o n cap ok Hi) as Hg2.
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1].
      2: { destruct Hg as (G1 & G2). unfold cl. cbn [fst snd]. split; [exact G1|].
           destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v r E; discriminate]). }
      destruct Hg as (G1 & G2 & G3). destruct Hg2 as (H1 & H2 & H3 & _).
      pose proof (K_le n cap1 G2 H3) as HK1.
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (name_chg o y ok1) as Hn. unfold pspec in Hn.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2]; cbn [fst snd] in Hn; destruct Hn as (N1 & N2 & N3).
      2: { unfold cl. cbn [fst snd]. rewrite chg_app. split; [shp|].
           destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v r E; discriminate]). }
      specialize (N3 nm y1 eq_refl).
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (IHv d y1 ok2) as Hv. unfold pspec in Hv.
      destruct (jrv sm f d y1 ok2) as [[[[v r]|] tv] ok3]; cbn [fst snd] in Hv; destruct Hv as (V1 & V2 & V3).
      2: { unfold cl. cbn [fst snd]. rewrite !chg_app. split; [shp|].
           destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v r E; discriminate]). }
      specialize (V3 v r eq_refl).
      cbv beta iota.
      destruct (skip r) as [|c r1] eqn:Er; cbv beta iota.
      { unfold jrefuse, cl. cbn [fst snd]. rewrite !chg_app. cbn [chg]. split; [shp|].
        destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v' r' E; discriminate]). }
      assert (Hsr : length (c :: r1) <= length r) by (rewrite <- Er; apply skip_len). cbn [length] in Hsr.
      destruct (c =? 44)%Z; cbv beta iota.
      { pose proof (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 H1 G2) as Hl.
        destruct (jrl sm f d o (S n) cap1 ((nm, v) :: acc) r1 ok3) as [[res t'] ok4].
        unfold cl in Hl |- *. cbn [fst snd] in Hl |- *. destruct Hl as (L1 & L2 & L3).
        rewrite !chg_app. split; [shp|].
        destruct o; cbn [Nat.b2n] in *;
          (split; [lia|intros v' r' Hr; specialize (L3 v' r' Hr); lia]). }
      destruct (c =? closer o)%Z; cbv beta iota.
      { unfold jret, cl. cbn [fst snd]. rewrite !chg_app. cbn [chg]. split; [shp|].
        destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v' r' E; injection E as _ <-; lia]). }
      { unfold jrefuse, cl. cbn [fst snd]. rewrite !chg_app. cbn [chg]. split; [shp|].
        destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v' r' E; discriminate]). }
Qed.

Lemma jr_value_chg : forall d x ok, pspec 0 (length x) (length x + 3 * (MAXD - d)) (jr_value sm d x ok).
Proof. intros d x ok. unfold jr_value. apply (proj1 (chg_fuel _)). Qed.

Theorem jr_run_charge : forall x ok, (chg (snd (jr_run sm x ok)) <= length x + 3 * MAXD)%nat.
Proof.
  intros x ok. rewrite jr_run_eq. cbn [snd].
  destruct (jr_value_chg 0 x ok) as (_ & H & _). lia.
Qed.

Theorem jr_run_charge_ok : forall x ok t, fst (jr_run sm x ok) = Some t ->
  (chg (snd (jr_run sm x ok)) <= length x)%nat.
Proof.
  intros x ok t H. rewrite jr_run_eq in *. cbn [fst snd] in *.
  pose proof (jr_value_chg 0 x ok) as Hc.
  destruct (jr_value sm 0 x ok) as [[[[v r]|] tr] ok'].
  - unfold pspec in Hc. cbn [fst snd] in Hc |- *. destruct Hc as (_ & _ & Hc).
    specialize (Hc v r eq_refl). lia.
  - cbn [fst post] in H. discriminate.
Qed.

Theorem jr_run_shape : forall x ok, Forall ev_shape (snd (jr_run sm x ok)).
Proof. intros x ok. rewrite jr_run_eq. cbn [snd]. exact (proj1 (jr_value_chg 0 x ok)). Qed.

(* Per class: if every event whose request satisfies P charges at least m > 0, a parse has at most
   (length x + 3 * MAXD) / m such events; the same for the grow events alone, and for the other events alone. *)
Theorem jr_run_cnt : forall (P : nat -> bool) m x ok, (0 < m)%nat ->
  (forall e, ev_shape e -> match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end) ->
  (cntR P (snd (jr_run sm x ok)) <= (length x + 3 * MAXD) / m)%nat.
Proof.
  intros P m x ok Hm H. apply Nat.div_le_lower_bound; [lia|].
  eapply Nat.le_trans; [apply (cnt_by_charge P m _ (jr_run_shape x ok) H)|apply jr_run_charge].
Qed.

Theorem jr_run_cntG : forall (P : nat -> bool) m x ok, (0 < m)%nat ->
  (forall e, ev_shape e -> is_grow e = true ->
     match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end) ->
  (cntG P (snd (jr_run sm x ok)) <= (length x + 3 * MAXD) / m)%nat.
Proof.
  intros P m x ok Hm H. apply Nat.div_le_lower_bound; [lia|]. unfold cntG.
  eapply Nat.le_trans; [apply cnt_by_charge_in|eapply Nat.le_trans; [apply chg_filter_le|apply jr_run_charge]].
  pose proof (jr_run_shape x ok) as Hs. rewrite Forall_forall in Hs |- *. intros e He.
  apply filter_In in He as [He Hg]. exact (H e (Hs e He) Hg).
Qed.

Theorem jr_run_cntS : forall (P : nat -> bool) m x ok, (0 < m)%nat ->
  (forall e, ev_shape e -> is_grow e = false ->
     match req_ev e with Some r => P r = true -> (m <= chg_ev e)%nat | None => True end) ->
  (cntS P (snd (jr_run sm x ok)) <= (length x + 3 * MAXD) / m)%nat.
Proof.
  intros P m x ok Hm H. apply Nat.div_le_lower_bound; [lia|]. unfold cntS.
  eapply Nat.le_trans; [apply cnt_by_charge_in|eapply Nat.le_trans; [apply chg_filter_le|apply jr_run_charge]].
  pose proof (jr_run_shape x ok) as Hs. rewrite Forall_forall in Hs |- *. intros e He.
  apply filter_In in He as [He Hg]. apply negb_true_iff in Hg. exact (H e (Hs e He) Hg).
Qed.

(* An accepted parse's grow events: a container's items grow its arrays as tgo does, whatever the items' text. *)

Lemma cont_grows : forall f d o b y ok v r tr ok',
  (forall d o n cap acc y ok v r tr ok', jrl sm f d o n cap acc y ok = (Some (v, r), tr, ok') ->
     exists L, v = mk o (rev acc ++ L) /\ filter is_grow tr = filter is_grow (tgo o n cap L)) ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (v, r), tr, ok') -> filter is_grow tr = filter is_grow (ttrace v).
Proof.
  intros f d o b y ok v r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H.
  destruct (skip y) as [|c r0]; cbv beta iota in H.
  - destruct (IHl _ _ _ _ _ _ _ _ _ _ _ H) as (L & -> & E). rewrite E, tgo_mk. reflexivity.
  - destruct (c =? closer o)%Z; cbv beta iota in H.
    + unfold jret in H. injection H; intros; subst. destruct o; reflexivity.
    + destruct (IHl _ _ _ _ _ _ _ _ _ _ _ H) as (L & -> & E). rewrite E, tgo_mk. reflexivity.
Qed.

Lemma grows_fuel : forall f,
  (forall d x ok v r tr ok', jrv sm f d x ok = (Some (v, r), tr, ok') ->
     filter is_grow tr = filter is_grow (ttrace v)) /\
  (forall d o n cap acc y ok v r tr ok', jrl sm f d o n cap acc y ok = (Some (v, r), tr, ok') ->
     exists L, v = mk o (rev acc ++ L) /\ filter is_grow tr = filter is_grow (tgo o n cap L)).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok v r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (b =? 123)%Z; cbv beta iota in H; [exact (cont_grows f d true b y ok v r tr ok' IHl H)|].
      destruct (b =? 91)%Z; cbv beta iota in H; [exact (cont_grows f d false b y ok v r tr ok' IHl H)|].
      destruct (b =? 34)%Z; cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & ->).
        pose proof (jr_string_spec y ok) as Hs. rewrite Hj in Hs. destruct Hs as (q & _ & _ & -> & _).
        cbv beta iota in H. unfold jret in H. injection H; intros; subst. reflexivity. }
      destruct (b =? 116)%Z; cbv beta iota in H.
      { destruct (lit_grows _ _ _ _ _ _ _ _ H) as [-> ->]. reflexivity. }
      destruct (b =? 102)%Z; cbv beta iota in H.
      { destruct (lit_grows _ _ _ _ _ _ _ _ H) as [-> ->]. reflexivity. }
      destruct (b =? 110)%Z; cbv beta iota in H.
      { destruct (lit_grows _ _ _ _ _ _ _ _ H) as [-> ->]. reflexivity. }
      pose proof (jr_number_spec sm (b :: y) ok ltac:(discriminate)) as Hn. rewrite H in Hn.
      destruct Hn as (k & -> & _).
      destruct (jr_number_good _ _ _ _ _ _ _ H) as (txt & -> & _). reflexivity.
    + intros d o n cap acc y ok v r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & Eg & H & ->). cbv beta in H.
      destruct (grow_some o n cap ok cap1 tg ok1 Eg) as [-> ->].
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & ->). cbv beta iota in H.
      apply jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & ->). cbv beta iota in H.
      assert (Hn : filter is_grow tn = []).
      { pose proof (jr_name_spec o y ok1) as Hs. rewrite En in Hs.
        destruct o; [destruct Hs as (q & -> & _)|destruct Hs as [-> _]]; reflexivity. }
      pose proof (IHv d y1 ok2 v0 r0 tv ok3 Ev) as Gv.
      destruct (skip r0) as [|c r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (c =? 44)%Z; cbv beta iota in H.
      { destruct (IHl d o (S n) (gcap n cap) ((nm, v0) :: acc) r1 ok3 v r t4 ok' H) as (L & -> & E).
        exists ((nm, v0) :: L). split.
        - cbn [rev]. rewrite <- app_assoc. reflexivity.
        - rewrite tgo_cons, !fg_app, Hn, Gv, E. reflexivity. }
      destruct (c =? closer o)%Z; cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H; intros; subst.
      exists [(nm, v0)]. split; [reflexivity|].
      rewrite tgo_cons, tgo_nil, !fg_app, Hn, Gv. reflexivity.
Qed.

Theorem jr_run_grows_eq : forall x ok t, fst (jr_run sm x ok) = Some t ->
  filter is_grow (snd (jr_run sm x ok)) = filter is_grow (ttrace t).
Proof.
  intros x ok t H. rewrite jr_run_eq in *. cbn [fst snd] in *.
  destruct (jr_value sm 0 x ok) as [[[[v r]|] tr] ok'] eqn:E; cbn [fst snd post] in H |- *; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. exact (proj1 (grows_fuel _) 0 x ok v r tr ok' E).
Qed.

End C.

Theorem jr_run_grows_tree : forall sm x ok t, fst (jr_run sm x ok) = Some t ->
  forall P, cntG P (snd (jr_run sm x ok)) = cntG P (ttrace t).
Proof. intros sm x ok t H P. unfold cntG. rewrite (jr_run_grows_eq sm x ok t H). reflexivity. Qed.
