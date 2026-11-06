(* omx-clap-core/fuzz_preset, Spec: the live SECONDARY blocks and the live class-24 blocks of target_run's calls, derived
   in P8's vocabulary (PresetRun.hruns / hlive), for h-pre-b1's non-primary room invariant (h-hpreset-7, LiveSetBounds).

   WHAT IT SAYS. At every position i of target_run's calls on an input x of at most MAXB = 3 MiB bytes (any number of
   calls, any grants of check_no_overread's three readings):
     live_sec : the live requests above the largest primary class (PresetRoom.is_primary = false, i.e. >= 64,513
                bytes: primary_iff) number at most LSEC = 9,521 (LSEC_value);
     live_c24 : the live requests of class 24 (5,889 .. 7,936 bytes) number at most L24 = 146,219 (L24_value).
   live_sec_state / live_c24_state add the driver's at most DRV = 3 blocks (the form PresetP8.preset_room's
   allocator-state premise has). LSEC_side: LSEC + DRV + QT / 64513 = 9,521 + 3 + 4,177 < 16,000. L24_room: class 24
   is the batch class, and L24 + DRV with the quarantine's and the batch records' most fits it (224,817 of 458,752).
   The closed forms, in MAXB (MAXD = 32 gives the 96):
     LSEC = 3 + max (3 A) (A + 2 B + 2),  A = (MAXB + 96) / 1024,  B = (MAXB + 96) / 1024 + (3 MAXB + 96) / 64496 + 4
     L24  = 3 + max (3 A) (A + 2 B + 2),  A = (MAXB + 96) / 66,    B = (MAXB + 96) / 66   + (3 MAXB + 96) / 5872  + 4

   HOW. PresetGate.g_hruns_live bounds the live count of ANY request predicate f by 3 + max (3 A) (A + 2 B + 2), A
   bounding the f-requests of one reading of x and B those of the file tree's trace and its rewritten copy. PjCharge
   bounds A and B by charges: an event of charge >= m occurs at most (|x| + 3 MAXD) / m times. Its per-event charge
   is too weak for the secondaries: the kids array's grow to capacity 2048 (the 114,688-byte, first secondary request)
   charges 512, which gives 18,737 (LSEC_unweighted_value), above 16,000 - 4,177. The bytes that pay for that grow's
   EARLIER grows (8 .. 1024, charge 514) are spent on primary requests and count for nothing there.
   So this file re-runs PjCharge's charge induction with a WEIGHTED charge wev jT: a grow to a capacity below
   wT = 8 * 2 ^ jT weighs 0, the grow to wT weighs PjCharge.K wT (the whole chain's charge), a larger grow weighs its
   own charge (Kw_grow: the weights of a chain add up to Kw <= K, so the same budget pays). Every other event weighs
   its charge (wev_nongrow). jr_run_wcharge: a parse's weight is at most |x| + 3 MAXD, under any grants.
   - secondaries, jT = 8 (wT = 2048): every secondary request weighs >= 1024 (sec_min: kids grow to 2048 weighs
     K 2048 = 1026, larger kids grows >= 1024, keys grows >= 8192 weigh >= 2048, an allocation >= 64,496);
   - class 24, jT = 4 (wT = 128): every class-24 grow weighs >= 66 = K 128 (c24_tab, checked by computation), every
     class-24 allocation charges >= lo 24 - 17 = 5,872 (lo24).
   w_reads / w_core are PresetGate.g_reads / g_core with the weighted grow count.

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss PjCharge PresetRun PresetRoom PresetGate.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
Import ListNotations.

(* ================================================================ part 1: the weighted charge (nat) *)

Section Weight.
Local Open Scope nat_scope.

Variable jT : nat.

Definition wT : nat := 8 * 2 ^ jT.

(* the weight of a grow (kids or keys) to capacity c, and of all its grows up to capacity c *)
Definition Wc (c : nat) : nat :=
  if Nat.ltb c wT then 0 else if Nat.eqb c wT then PjCharge.K wT else PjCharge.gchg c.
Definition Kw (c : nat) : nat := if Nat.ltb c wT then 0 else PjCharge.K c.

Definition wev (e : ev) : nat :=
  match e with
  | EAlloc n => Nat.max (n - 1) 1
  | EGrow _ n => if Nat.eqb (n mod 7) 0 then Wc (n / 56) else Wc (n / 8)
  | EFail _ | EFree _ => 0
  end.

Fixpoint wchg (t : list ev) : nat := match t with [] => 0 | e :: r => wev e + wchg r end.

Lemma wT_ge8 : 8 <= wT.
Proof. unfold wT. pose proof (pow2_pos jT). lia. Qed.

Lemma Kw0 : Kw 0 = 0.
Proof. unfold Kw. destruct (Nat.ltb 0 wT); reflexivity. Qed.

Lemma Kw_le_K : forall c, Kw c <= PjCharge.K c.
Proof. intros c. unfold Kw. destruct (Nat.ltb c wT); lia. Qed.

Lemma Kw_le : forall n cap, capok cap -> cap <= Nat.max 8 (2 * n) -> Kw cap <= n + 2.
Proof. intros n cap Hc H. pose proof (K_le n cap Hc H). pose proof (Kw_le_K cap). lia. Qed.

Lemma wev_nongrow : forall e, is_grow e = false -> wev e = chg_ev e.
Proof. intros [n|m n|n|n] H; cbn [is_grow] in H; try discriminate; reflexivity. Qed.

Lemma wchg_kids : forall m c, wev (EGrow m (56 * c)) = Wc c.
Proof.
  intros m c. unfold wev.
  assert (E1 : (56 * c) mod 7 = 0).
  { pose proof (Nat.div_mod_eq (56 * c) 7). pose proof (Nat.mod_upper_bound (56 * c) 7 ltac:(discriminate)).
    set (q := (56 * c) / 7) in *. set (r := (56 * c) mod 7) in *. clearbody q r. lia. }
  assert (E2 : 56 * c / 56 = c).
  { pose proof (Nat.div_mod_eq (56 * c) 56). pose proof (Nat.mod_upper_bound (56 * c) 56 ltac:(discriminate)).
    set (q := (56 * c) / 56) in *. set (r := (56 * c) mod 56) in *. clearbody q r. lia. }
  rewrite E1, E2. reflexivity.
Qed.

Lemma wchg_keys : forall m c, capok c -> c <> 0 -> wev (EGrow m (8 * c)) = Wc c.
Proof.
  intros m c [->|[j ->]] Hc; [contradiction|].
  pose proof (pow2_mod7 j). pose proof (pow2_pos j). set (p := 2 ^ j) in *. clearbody p.
  unfold wev.
  assert (E1 : (8 * (8 * p)) mod 7 <> 0).
  { pose proof (Nat.div_mod_eq (8 * (8 * p)) 7). pose proof (Nat.mod_upper_bound (8 * (8 * p)) 7 ltac:(discriminate)).
    pose proof (Nat.div_mod_eq p 7). pose proof (Nat.mod_upper_bound p 7 ltac:(discriminate)).
    set (q := (8 * (8 * p)) / 7) in *. set (r := (8 * (8 * p)) mod 7) in *.
    set (q' := p / 7) in *. set (r' := p mod 7) in *. clearbody q r q' r'. lia. }
  assert (E2 : 8 * (8 * p) / 8 = 8 * p).
  { pose proof (Nat.div_mod_eq (8 * (8 * p)) 8). pose proof (Nat.mod_upper_bound (8 * (8 * p)) 8 ltac:(discriminate)).
    set (q := (8 * (8 * p)) / 8) in *. set (r := (8 * (8 * p)) mod 8) in *. clearbody q r. lia. }
  destruct (Nat.eqb_spec ((8 * (8 * p)) mod 7) 0) as [E|E]; [contradiction|].
  rewrite E2. reflexivity.
Qed.

(* the weights of a grow chain add up to Kw, as the charges add up to K (PjCharge.K_grow) *)
Lemma Kw_grow : forall cap, capok cap -> Kw cap + Wc (ncap cap) = Kw (ncap cap).
Proof.
  intros cap [->|[j ->]].
  - change (ncap 0) with 8. rewrite Kw0. pose proof wT_ge8 as H8. unfold Wc, Kw.
    destruct (Nat.ltb_spec 8 wT) as [H|H]; [reflexivity|].
    assert (E : wT = 8) by lia. rewrite E. reflexivity.
  - pose proof (pow2_pos j) as Hp.
    destruct (K_grow (8 * 2 ^ j) ltac:(right; exists j; reflexivity)) as (_ & _ & HK).
    rewrite ncap_pos in HK by lia. rewrite ncap_pos by lia.
    unfold Wc, Kw, wT.
    destruct (Nat.lt_ge_cases (S j) jT) as [Hlt|Hge].
    + assert (Hpow : 2 ^ S j < 2 ^ jT) by (apply Nat.pow_lt_mono_r; lia).
      change (2 ^ S j) with (2 * 2 ^ j) in Hpow.
      set (p := 2 ^ j) in *. set (q := 2 ^ jT) in *. clearbody p q.
      destruct (Nat.ltb_spec (8 * p) (8 * q)); [|lia].
      destruct (Nat.ltb_spec (2 * (8 * p)) (8 * q)); [|lia]. reflexivity.
    + destruct (Nat.eq_dec (S j) jT) as [Heq|Hne].
      * rewrite <- Heq. change (2 ^ S j) with (2 * 2 ^ j).
        set (p := 2 ^ j) in *. clearbody p.
        destruct (Nat.ltb_spec (8 * p) (8 * (2 * p))); [|lia].
        destruct (Nat.ltb_spec (2 * (8 * p)) (8 * (2 * p))); [lia|].
        destruct (Nat.eqb_spec (2 * (8 * p)) (8 * (2 * p))); [|lia].
        replace (2 * (8 * p)) with (8 * (2 * p)) by lia. lia.
      * assert (Hle : jT <= j) by lia.
        assert (Hpow : 2 ^ jT <= 2 ^ j) by (apply Nat.pow_le_mono_r; lia).
        set (p := 2 ^ j) in *. set (q := 2 ^ jT) in *. clearbody p q.
        destruct (Nat.ltb_spec (8 * p) (8 * q)); [lia|].
        destruct (Nat.ltb_spec (2 * (8 * p)) (8 * q)); [lia|].
        destruct (Nat.eqb_spec (2 * (8 * p)) (8 * q)); [lia|].
        exact HK.
Qed.

Lemma wchg_app : forall a b, wchg (a ++ b) = wchg a + wchg b.
Proof. induction a as [|e r IH]; intros b; cbn [wchg app]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma wchg_filter_le : forall f t, wchg (filter f t) <= wchg t.
Proof.
  intros f t. induction t as [|e r IH]; cbn [filter wchg]; [lia|]. destruct (f e); cbn [wchg]; lia.
Qed.

(* ---------------------------------------------------------------- PjCharge's induction, with wchg / Kw
   (each lemma is PjCharge's of the same name without the w, its proof with chg -> wchg, chg_ev -> wev, K -> Kw) *)

Definition wpspec {A : Type} (e L B : nat) (res : option (A * list Z) * list ev * list bool) : Prop :=
  Forall ev_shape (snd (fst res)) /\ (wchg (snd (fst res)) <= B)%nat /\
  (forall v r, fst (fst res) = Some (v, r) -> (wchg (snd (fst res)) + length r + e <= L)%nat).

Lemma wpspec_refuse : forall A e L B ok, @wpspec A e L B (None, [], ok).
Proof.
  intros A e L B ok. unfold wpspec. cbn [fst snd wchg]. split; [constructor|]. split; [lia|].
  intros v r H. discriminate.
Qed.

Lemma wpspec_weak : forall A e L B e' L' B' (res : option (A * list Z) * list ev * list bool),
  wpspec e L B res -> (B <= B')%nat -> (L + e' <= L' + e)%nat -> wpspec e' L' B' res.
Proof.
  intros A e L B e' L' B' res (H1 & H2 & H3) HB HL. split; [exact H1|]. split; [lia|].
  intros v r Hr. specialize (H3 v r Hr). lia.
Qed.

Definition wcl (o : bool) (n cap : nat) (y : list Z) (d : nat) (res : option (jv * list Z) * list ev * list bool)
  : Prop :=
  Forall ev_shape (snd (fst res)) /\
  (wchg (snd (fst res)) + (1 + Nat.b2n o) * Kw cap <=
     length y + 1 + n + Nat.b2n o * (2 * n) + 3 + 3 * (MAXD - d))%nat /\
  (forall v r, fst (fst res) = Some (v, r) ->
     (wchg (snd (fst res)) + (1 + Nat.b2n o) * Kw cap + length r <= length y + 1 + n + Nat.b2n o * (2 * n))%nat).

Lemma wgrow_chg : forall o n cap ok, inv n cap -> capok cap ->
  match grow o n cap ok with
  | (Some cap1, t, _) => Forall ev_shape t /\ capok cap1 /\
      wchg t + (1 + Nat.b2n o) * Kw cap = (1 + Nat.b2n o) * Kw cap1
  | (None, t, _) => Forall ev_shape t /\ wchg t + (1 + Nat.b2n o) * Kw cap <= (1 + Nat.b2n o) * (n + 2)
  end.
Proof.
  intros o n cap ok Hi Hc. unfold grow.
  destruct (Nat.ltb n cap) eqn:E.
  - unfold jret. cbn [wchg]. split; [constructor|]. split; [exact Hc|]. lia.
  - apply Nat.ltb_ge in E. destruct Hi as (Hi1 & Hi2 & Hi3 & Hi4).
    assert (n = cap) by lia. subst n.
    destruct (K_grow cap Hc) as (C1 & C2 & C3).
    pose proof (Kw_grow cap Hc) as W3.
    cbv zeta. change (if Nat.eqb cap 0 then 8 else 2 * cap) with (ncap cap).
    assert (Hk : Kw (ncap cap) <= cap + 2).
    { apply Kw_le; [exact C1|]. unfold ncap. destruct (Nat.eqb cap 0); lia. }
    unfold jbind. cbv beta.
    destruct (jrealloc_cases (56 * cap) (56 * ncap cap) ok) as [E1|E1]; rewrite E1; cbv beta iota.
    + destruct o; cbv beta iota.
      * destruct (jrealloc_cases (8 * cap) (8 * ncap cap) (tl ok)) as [E2|E2]; rewrite E2; cbv beta iota.
        -- unfold jret. cbn [app wchg Nat.b2n]. rewrite wchg_kids, (wchg_keys _ _ C1 C2).
           split; [shp|]. split; [exact C1|]. lia.
        -- cbn [app wchg Nat.b2n]. rewrite wchg_kids. cbn [wev]. split; [shp|]. lia.
      * unfold jret. cbn [app wchg Nat.b2n]. rewrite wchg_kids. split; [shp|]. split; [exact C1|]. lia.
    + cbn [wchg wev]. split; [shp|]. destruct o; cbn [Nat.b2n]; lia.
Qed.

Lemma wstr_chg : forall z ok, wpspec 0 (length z) (length z) (jr_string z ok).
Proof.
  intros z ok. unfold jr_string.
  destruct (scan z) as [q|] eqn:Es; cbv beta iota; [|apply wpspec_refuse].
  pose proof (scan_quote z q Es) as [Hq _].
  unfold jbind, jalloc, take.
  destruct ok as [|b ok]; [|destruct b]; cbv beta iota.
  - destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota.
    + destruct (decode_stop z s r Ed) as (q' & Es' & Hr & _). rewrite Es in Es'. injection Es' as <-.
      unfold jret, wpspec. cbn [fst snd app wchg wev]. split; [shp|]. split; [lia|].
      intros s' r' E. injection E as _ <-. rewrite Hr, length_skipn. lia.
    + unfold jfree, jrefuse, wpspec. cbn [fst snd app wchg wev]. split; [shp|]. split; [lia|].
      intros s' r' E. discriminate.
  - destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota.
    + destruct (decode_stop z s r Ed) as (q' & Es' & Hr & _). rewrite Es in Es'. injection Es' as <-.
      unfold jret, wpspec. cbn [fst snd app wchg wev]. split; [shp|]. split; [lia|].
      intros s' r' E. injection E as _ <-. rewrite Hr, length_skipn. lia.
    + unfold jfree, jrefuse, wpspec. cbn [fst snd app wchg wev]. split; [shp|]. split; [lia|].
      intros s' r' E. discriminate.
  - unfold wpspec. cbn [fst snd wchg wev]. split; [shp|]. split; [lia|]. intros s' r' E. discriminate.
Qed.

Lemma wname_chg : forall o y ok, wpspec (2 * Nat.b2n o) (length y) (length y) (jr_name o y ok).
Proof.
  intros o y ok. destruct o.
  2: { unfold jr_name, jret, wpspec. cbn [fst snd wchg Nat.b2n]. split; [constructor|]. split; [lia|].
       intros nm y1 E. injection E as _ <-. lia. }
  unfold jr_name. cbv beta iota.
  destruct (skip y) as [|b z] eqn:Ey; cbv beta iota; [apply wpspec_refuse|].
  assert (Hy : length (b :: z) <= length y) by (rewrite <- Ey; apply skip_len). cbn [length] in Hy.
  destruct (b =? 34)%Z; cbv beta iota; [|apply wpspec_refuse].
  unfold jbind at 1. cbv beta.
  pose proof (wstr_chg z ok) as Hs. unfold wpspec in Hs.
  destruct (jr_string z ok) as [[[[nm r]|] t] ok1]; cbn [fst snd] in Hs; destruct Hs as (S1 & S2 & S3);
    cbv beta iota.
  - specialize (S3 nm r eq_refl).
    destruct (skip r) as [|c r1] eqn:Er; cbv beta iota.
    + unfold jbind, jfree, jrefuse, wpspec. cbn [fst snd app]. rewrite wchg_app. cbn [wchg wev].
      split; [shp|]. split; [lia|]. intros nm' y1 E. discriminate.
    + assert (Hr : length (c :: r1) <= length r) by (rewrite <- Er; apply skip_len). cbn [length] in Hr.
      destruct (c =? 58)%Z; cbv beta iota.
      * unfold jret, wpspec. cbn [fst snd Nat.b2n]. rewrite app_nil_r.
        split; [exact S1|]. split; [lia|]. intros nm' y1 E. injection E as _ <-. lia.
      * unfold jbind, jfree, jrefuse, wpspec. cbn [fst snd app]. rewrite wchg_app. cbn [wchg wev].
        split; [shp|]. split; [lia|]. intros nm' y1 E. discriminate.
  - unfold wpspec. cbn [fst snd]. split; [exact S1|]. split; [lia|]. intros nm' y1 E. discriminate.
Qed.

Lemma wlit_chg : forall w v x ok, w <> [] -> wpspec 0 (length x) (length x) (lit w v x ok).
Proof.
  intros w v x ok Hw. pose proof (lit_spec w v x ok Hw) as H.
  destruct (lit w v x ok) as [[[[u r]|] t] ok'].
  - destruct H as [-> Hr]. unfold wpspec. cbn [fst snd wchg]. split; [constructor|]. split; [lia|].
    intros v' r' E. injection E as _ <-. lia.
  - subst t. apply wpspec_refuse.
Qed.

Lemma wcont_chg : forall loop d o b y ok,
  (forall o' n cap acc y' ok', inv n cap -> capok cap -> wcl o' n cap y' (S d) (loop (S d) o' n cap acc y' ok')) ->
  wpspec 0 (length (b :: y)) (length (b :: y) + 3 * (MAXD - d)) (jr_cont loop d o (b :: y) ok).
Proof.
  intros loop d o b y ok HL. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; cbv beta iota; [apply wpspec_refuse|].
  apply Nat.ltb_ge in Ed. cbn [tl]. cbv zeta.
  assert (Hloop : wpspec 0 (length (b :: y)) (length (b :: y) + 3 * (MAXD - d)) (loop (S d) o 0 0 [] (skip y) ok)).
  { assert (Hi : inv 0 0) by (unfold inv; lia).
    assert (Hc : capok 0) by (left; reflexivity).
    pose proof (skip_len y) as Hy.
    destruct (HL o 0 0 [] (skip y) ok Hi Hc) as (A & B & C).
    rewrite Kw0 in B, C.
    unfold wpspec. cbn [length]. split; [exact A|]. split; [lia|].
    intros v r Hr. specialize (C v r Hr). lia. }
  destruct (skip y) as [|c r] eqn:Ey; cbv beta iota; [exact Hloop|].
  assert (Hy : length (c :: r) <= length y) by (rewrite <- Ey; apply skip_len). cbn [length] in Hy.
  destruct (c =? closer o)%Z; cbv beta iota; [|exact Hloop].
  unfold jret, wpspec. cbn [fst snd wchg length]. split; [constructor|]. split; [lia|].
  intros v r' Hr. injection Hr as _ <-. lia.
Qed.

(* the weighted form of PjCharge.chk_minG: the grows of ev_shape checked one by one for j <= J *)
Definition wchk_minG (P : nat -> bool) (m hi J : nat) : bool :=
  forallb (fun j =>
    implb (P (448 * 2 ^ j + 16)) (Nat.leb m (wev (EGrow 0 (448 * 2 ^ j)))) &&
    implb (P (64 * 2 ^ j + 16)) (Nat.leb m (wev (EGrow 0 (64 * 2 ^ j))))) (seq 0 (S J)) &&
  Nat.ltb hi (64 * 2 ^ (S J) + 16).

Lemma wchk_minG_ok : forall P m hi J, wchk_minG P m hi J = true -> (forall r, P r = true -> (r <= hi)%nat) ->
  forall e, ev_shape e -> is_grow e = true ->
  match req_ev e with Some r => P r = true -> (m <= wev e)%nat | None => True end.
Proof.
  intros P m hi J H HR e He Hg. unfold wchk_minG in H.
  apply andb_true_iff in H as [H2 H3]. apply Nat.ltb_lt in H3. rewrite forallb_forall in H2.
  destruct e as [n|m0 n|n|n]; cbn [is_grow] in Hg; try discriminate.
  cbn [req_ev]. intros HP. pose proof (HR _ HP) as Hhi.
  change (wev (EGrow m0 n)) with (wev (EGrow 0 n)).
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

Lemma wcnt_by_charge_in : forall (P : nat -> bool) m t,
  Forall (fun e => match req_ev e with Some r => P r = true -> (m <= wev e)%nat | None => True end) t ->
  (m * cntR P t <= wchg t)%nat.
Proof.
  intros P m t Ht. induction Ht as [|e t He Ht IH]; cbn [cntR wchg]; [lia|]. cbv beta in He.
  destruct (req_ev e) as [q|]; [|lia].
  destruct (P q); [|lia].
  specialize (He eq_refl). rewrite Nat.mul_succ_r. lia.
Qed.

Section C.

Variable sm : list Z -> Z * Z.

Lemma wnum_chg : forall x ok, x <> [] -> wpspec 0 (length x) (length x) (jr_number sm x ok).
Proof.
  intros x ok Hx. unfold jr_number. cbv beta zeta.
  set (j := match x with b :: _ => if (b =? 45)%Z then 1 else 0 | [] => 0 end).
  assert (Hj : j <= length x).
  { unfold j. destruct x as [|b x']; [contradiction|]. cbn [length]. destruct (b =? 45)%Z; lia. }
  clearbody j.
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c z] eqn:Ez; cbv beta iota; [apply wpspec_refuse|].
  destruct (negb (digit c)); cbv beta iota; [apply wpspec_refuse|].
  destruct ((c =? 48)%Z && match z with c1 :: _ => digit c1 | [] => false end)%bool; cbv beta iota;
    [apply wpspec_refuse|].
  destruct (span numch z) as [a r] eqn:Es; cbv beta iota.
  pose proof (span_app _ _ _ _ Es) as Hz.
  assert (Ht : length (firstn j x ++ c :: a) + length r = length x).
  { rewrite length_app, length_firstn. cbn [length]. cbn [length] in Hsk.
    rewrite Hz, length_app in Hsk. lia. }
  assert (Ht1 : 1 <= length (firstn j x ++ c :: a)) by (rewrite length_app; cbn [length]; lia).
  set (txt := firstn j x ++ c :: a) in *. clearbody txt.
  unfold jbind, jalloc, take.
  destruct ok as [|b ok]; [|destruct b]; cbv beta iota.
  - destruct (whole sm txt); unfold jret, jrefuse, wpspec; cbn [fst snd app wchg wev].
    + split; [shp|]. split; [lia|]. intros v r' E. injection E as _ <-. lia.
    + split; [shp|]. split; [lia|]. intros v r' E. discriminate.
  - destruct (whole sm txt); unfold jret, jrefuse, wpspec; cbn [fst snd app wchg wev].
    + split; [shp|]. split; [lia|]. intros v r' E. injection E as _ <-. lia.
    + split; [shp|]. split; [lia|]. intros v r' E. discriminate.
  - unfold wpspec. cbn [fst snd wchg wev]. split; [shp|]. split; [lia|]. intros v r' E. discriminate.
Qed.

Lemma wchg_fuel : forall f,
  (forall d x ok, wpspec 0 (length x) (length x + 3 * (MAXD - d)) (jrv sm f d x ok)) /\
  (forall d o n cap acc y ok, inv n cap -> capok cap -> wcl o n cap y d (jrl sm f d o n cap acc y ok)).
Proof.
  induction f as [|f [IHv IHl]].
  - split.
    + intros d x ok. apply wpspec_refuse.
    + intros d o n cap acc y ok Hi Hc. cbn [jrl]. unfold jrefuse, wcl. cbn [fst snd wchg].
      destruct Hi as (Hi1 & Hi2 & Hi3 & Hi4). pose proof (Kw_le n cap Hc Hi2) as HK.
      split; [constructor|]. destruct o; cbn [Nat.b2n]; (split; [lia|intros v r E; discriminate]).
  - split.
    + intros d x ok. cbn [jrv].
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota; [apply wpspec_refuse|].
      assert (Hsx : length (b :: y) <= length x) by (rewrite <- Ex; apply skip_len).
      apply (wpspec_weak _ 0 (length (b :: y)) (length (b :: y) + 3 * (MAXD - d))); [|lia|lia].
      destruct (b =? 123)%Z; cbv beta iota; [apply wcont_chg; intros; apply IHl; assumption|].
      destruct (b =? 91)%Z; cbv beta iota; [apply wcont_chg; intros; apply IHl; assumption|].
      destruct (b =? 34)%Z; cbv beta iota.
      * unfold jbind. cbv beta. pose proof (wstr_chg y ok) as Hs. unfold wpspec in Hs.
        destruct (jr_string y ok) as [[[[s r]|] t] ok1]; cbn [fst snd] in Hs; destruct Hs as (S1 & S2 & S3);
          cbv beta iota.
        -- specialize (S3 s r eq_refl). unfold jret, wpspec. cbn [fst snd]. rewrite app_nil_r.
           split; [exact S1|]. split; [cbn [length]; lia|].
           intros v r' Hr. injection Hr as _ <-. cbn [length]. lia.
        -- unfold wpspec. cbn [fst snd]. split; [exact S1|]. split; [cbn [length]; lia|].
           intros v r' Hr. discriminate.
      * destruct (b =? 116)%Z; cbv beta iota.
        { eapply wpspec_weak; [apply wlit_chg; discriminate|lia|lia]. }
        destruct (b =? 102)%Z; cbv beta iota.
        { eapply wpspec_weak; [apply wlit_chg; discriminate|lia|lia]. }
        destruct (b =? 110)%Z; cbv beta iota.
        { eapply wpspec_weak; [apply wlit_chg; discriminate|lia|lia]. }
        eapply wpspec_weak; [apply wnum_chg; discriminate|lia|lia].
    + intros d o n cap acc y ok Hi Hc. cbn [jrl]. unfold jbind at 1. cbv beta.
      pose proof (wgrow_chg o n cap ok Hi Hc) as Hg.
      pose proof (grow_spec o n cap ok Hi) as Hg2.
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1].
      2: { destruct Hg as (G1 & G2). unfold wcl. cbn [fst snd]. split; [exact G1|].
           destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v r E; discriminate]). }
      destruct Hg as (G1 & G2 & G3). destruct Hg2 as (H1 & H2 & H3 & _).
      pose proof (Kw_le n cap1 G2 H3) as HK1.
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (wname_chg o y ok1) as Hn. unfold wpspec in Hn.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2]; cbn [fst snd] in Hn; destruct Hn as (N1 & N2 & N3).
      2: { unfold wcl. cbn [fst snd]. rewrite wchg_app. split; [shp|].
           destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v r E; discriminate]). }
      specialize (N3 nm y1 eq_refl).
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (IHv d y1 ok2) as Hv. unfold wpspec in Hv.
      destruct (jrv sm f d y1 ok2) as [[[[v r]|] tv] ok3]; cbn [fst snd] in Hv; destruct Hv as (V1 & V2 & V3).
      2: { unfold wcl. cbn [fst snd]. rewrite !wchg_app. split; [shp|].
           destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v r E; discriminate]). }
      specialize (V3 v r eq_refl).
      cbv beta iota.
      destruct (skip r) as [|c r1] eqn:Er; cbv beta iota.
      { unfold jrefuse, wcl. cbn [fst snd]. rewrite !wchg_app. cbn [wchg]. split; [shp|].
        destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v' r' E; discriminate]). }
      assert (Hsr : length (c :: r1) <= length r) by (rewrite <- Er; apply skip_len). cbn [length] in Hsr.
      destruct (c =? 44)%Z; cbv beta iota.
      { pose proof (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 H1 G2) as Hl.
        destruct (jrl sm f d o (S n) cap1 ((nm, v) :: acc) r1 ok3) as [[res t'] ok4].
        unfold wcl in Hl |- *. cbn [fst snd] in Hl |- *. destruct Hl as (L1 & L2 & L3).
        rewrite !wchg_app. split; [shp|].
        destruct o; cbn [Nat.b2n] in *;
          (split; [lia|intros v' r' Hr; specialize (L3 v' r' Hr); lia]). }
      destruct (c =? closer o)%Z; cbv beta iota.
      { unfold jret, wcl. cbn [fst snd]. rewrite !wchg_app. cbn [wchg]. split; [shp|].
        destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v' r' E; injection E as _ <-; lia]). }
      { unfold jrefuse, wcl. cbn [fst snd]. rewrite !wchg_app. cbn [wchg]. split; [shp|].
        destruct o; cbn [Nat.b2n] in *; (split; [lia|intros v' r' E; discriminate]). }
Qed.

Lemma jr_value_wchg : forall d x ok, wpspec 0 (length x) (length x + 3 * (MAXD - d)) (jr_value sm d x ok).
Proof. intros d x ok. unfold jr_value. apply (proj1 (wchg_fuel _)). Qed.

(* a parse's weight, under any grants *)
Theorem jr_run_wcharge : forall x ok, (wchg (snd (jr_run sm x ok)) <= length x + 3 * MAXD)%nat.
Proof.
  intros x ok. rewrite jr_run_eq. cbn [snd].
  destruct (jr_value_wchg 0 x ok) as (_ & H & _). lia.
Qed.

(* PjCharge.jr_run_cnt / jr_run_cntG with the weight *)
Theorem jr_run_wcnt : forall (P : nat -> bool) m x ok, (0 < m)%nat ->
  (forall e, ev_shape e -> match req_ev e with Some r => P r = true -> (m <= wev e)%nat | None => True end) ->
  (cntR P (snd (jr_run sm x ok)) <= (length x + 3 * MAXD) / m)%nat.
Proof.
  intros P m x ok Hm H. apply Nat.div_le_lower_bound; [lia|].
  eapply Nat.le_trans; [|apply jr_run_wcharge].
  apply wcnt_by_charge_in. eapply Forall_impl; [|exact (jr_run_shape sm x ok)]. exact H.
Qed.

Theorem jr_run_wcntG : forall (P : nat -> bool) m x ok, (0 < m)%nat ->
  (forall e, ev_shape e -> is_grow e = true ->
     match req_ev e with Some r => P r = true -> (m <= wev e)%nat | None => True end) ->
  (cntG P (snd (jr_run sm x ok)) <= (length x + 3 * MAXD) / m)%nat.
Proof.
  intros P m x ok Hm H. apply Nat.div_le_lower_bound; [lia|]. unfold cntG.
  eapply Nat.le_trans; [apply wcnt_by_charge_in|eapply Nat.le_trans; [apply wchg_filter_le|apply jr_run_wcharge]].
  pose proof (jr_run_shape sm x ok) as Hs. rewrite Forall_forall in Hs |- *. intros e He.
  apply filter_In in He as [He Hg]. exact (H e (Hs e He) Hg).
Qed.

End C.

End Weight.

(* ================================================================ part 2: the live counts (Z) *)

Local Open Scope Z_scope.

(* ---------------------------------------------------------------- PresetGate.g_reads / g_core, weighted grows *)

Lemma w_reads : forall jT sm x (f : Z -> bool) (mG mS mA : nat), Z.of_nat (length x) <= MAXB ->
  (0 < mA)%nat -> (mA <= mG)%nat -> (mA <= mS)%nat ->
  (forall e, ev_shape e -> is_grow e = true ->
     match req_ev e with Some r => f (Z.of_nat r) = true -> (mG <= wev jT e)%nat | None => True end) ->
  (forall e, ev_shape e -> is_grow e = false ->
     match req_ev e with Some r => f (Z.of_nat r) = true -> (mS <= chg_ev e)%nat | None => True end) ->
  (forall ok, Z.of_nat (nprodR f (rd_hevs (rtr sm ok x))) <= (MAXB + 96) / Z.of_nat mA) /\
  (forall t, fst (jr_run sm x []) = Some t ->
     Z.of_nat (nprodR f (rd_hevs (ttrace t))) <=
     (MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS).
Proof.
  intros jT sm x f mG mS mA Hx Hpos HAG HAS HG HS.
  assert (HmG : (0 < mG)%nat) by lia.
  assert (HmS : (0 < mS)%nat) by lia.
  split.
  - intros ok. rewrite g_nprod_cntR. unfold rtr.
    apply (g_cnt_z _ (length x)); [exact Hpos|exact Hx|].
    apply (jr_run_wcnt jT sm); [exact Hpos|].
    intros e He. destruct (is_grow e) eqn:Eg.
    + specialize (HG e He Eg). revert HG. destruct (req_ev e) as [r|]; [|intros _; exact I].
      intros HG Hf. specialize (HG Hf). lia.
    + specialize (HS e He Eg). rewrite (wev_nongrow jT e Eg). revert HS.
      destruct (req_ev e) as [r|]; [|intros _; exact I].
      intros HS Hf. specialize (HS Hf). lia.
  - intros t Ht. rewrite g_nprod_cntR, cntR_split, Nat2Z.inj_add.
    assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ht).
    pose proof (jr_run_wcntG jT sm (fun r => f (Z.of_nat r)) mG x [] HmG HG) as G1.
    rewrite (jr_run_grows_tree sm x [] t Ht (fun r => f (Z.of_nat r))) in G1.
    pose proof (g_cnt_z _ _ _ MAXB HmG Hx G1) as ZG.
    pose proof (jr_run_cntS sm (fun r => f (Z.of_nat r)) mS (wdoc t false) [] HmS HS) as S1.
    rewrite (G9_trace sm t Hw false) in S1.
    assert (Hlw : Z.of_nat (length (wdoc t false)) <= 3 * MAXB).
    { pose proof (SlotSizes.wlen_false_read sm x t Ht) as W. unfold PjWriteHyp.wlen in W. lia. }
    pose proof (g_cnt_z _ _ _ (3 * MAXB) HmS Hlw S1) as ZS.
    lia.
Qed.

(* the live count of a request predicate f at every position of the calls *)
Lemma w_core : forall jT sm x os (f : Z -> bool) (mG mS mA : nat), Z.of_nat (length x) <= MAXB ->
  (0 < mA)%nat -> (mA <= mG)%nat -> (mA <= mS)%nat ->
  (forall e, ev_shape e -> is_grow e = true ->
     match req_ev e with Some r => f (Z.of_nat r) = true -> (mG <= wev jT e)%nat | None => True end) ->
  (forall e, ev_shape e -> is_grow e = false ->
     match req_ev e with Some r => f (Z.of_nat r) = true -> (mS <= chg_ev e)%nat | None => True end) ->
  forall i, Z.of_nat (cnt f (hlive (firstn i (hruns sm x os)))) <=
    3 + Z.max (3 * ((MAXB + 96) / Z.of_nat mA))
              ((MAXB + 96) / Z.of_nat mA + 2 * ((MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS + 4) + 2).
Proof.
  intros jT sm x os f mG mS mA Hx Hpos HAG HAS HG HS i.
  assert (HmG : (0 < mG)%nat) by lia.
  assert (HmS : (0 < mS)%nat) by lia.
  assert (Hz0 : 0 <= (MAXB + 96) / Z.of_nat mA) by (apply Z.div_pos; unfold MAXB; lia).
  assert (Hz1 : 0 <= (MAXB + 96) / Z.of_nat mG) by (apply Z.div_pos; unfold MAXB; lia).
  assert (Hz2 : 0 <= (3 * MAXB + 96) / Z.of_nat mS) by (apply Z.div_pos; unfold MAXB; lia).
  destruct (w_reads jT sm x f mG mS mA Hx Hpos HAG HAS HG HS) as [HA HBt].
  assert (HA' : forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= Z.to_nat ((MAXB + 96) / Z.of_nat mA))%nat)
    by (intros ok; specialize (HA ok); lia).
  assert (HB : forall t, fst (jr_run sm x []) = Some t ->
               (nprodR f (rd_hevs (ttrace t)) <=
                Z.to_nat ((MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS + 4))%nat)
    by (intros t Ht; specialize (HBt t Ht); lia).
  assert (HB' : forall ms, fst (jr_run sm x []) = Some (JObj ms) ->
                (nprodR f (rd_hevs (ttrace (copy_set ms))) <=
                 Z.to_nat ((MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS + 4))%nat)
    by (intros ms Hms; specialize (HBt (JObj ms) Hms); pose proof (g_nprod_copy f ms); lia).
  pose proof (g_hruns_live sm x os f _ _ HA' HB HB' i) as Hl.
  unfold KH, KB in Hl. lia.
Qed.

(* the allocator-state form: the model's live requests plus at most DRV = 3 driver blocks (PresetP8.preset_room) *)
Lemma cnt_le_len : forall (f : Z -> bool) l, (cnt f l <= length l)%nat.
Proof.
  intros f l. unfold cnt. induction l as [|z l IH]; cbn [List.filter length]; [lia|].
  destruct (f z); cbn [length]; lia.
Qed.

Lemma cnt_state : forall (f : Z -> bool) (L l d : list Z), (length d <= 3)%nat -> Permutation L (l ++ d) ->
  (cnt f L <= cnt f l + 3)%nat.
Proof.
  intros f L l d Hd Hp. rewrite (cnt_perm f _ _ Hp), cnt_app. pose proof (cnt_le_len f d). lia.
Qed.

(* ---------------------------------------------------------------- the secondaries *)

(* a request above the largest primary class (PresetRoom.is_primary: needed size <= 64 KiB) *)
Definition sec_req (n : Z) : bool := negb (is_primary n).

Lemma rz_size_lo : forall n, n <= 64512 -> rz_size n <= 1024.
Proof.
  intros n H. unfold rz_size, rz_log.
  destruct (n <=? 48); [apply Z.leb_le; reflexivity|].
  destruct (n <=? 96); [apply Z.leb_le; reflexivity|].
  destruct (n <=? 448); [apply Z.leb_le; reflexivity|].
  destruct (n <=? 3968); [apply Z.leb_le; reflexivity|].
  destruct (n <=? 16128); [apply Z.leb_le; reflexivity|].
  destruct (n <=? 32256); [apply Z.leb_le; reflexivity|].
  destruct (n <=? 64512) eqn:E; [apply Z.leb_le; reflexivity|].
  apply Z.leb_gt in E. lia.
Qed.

Lemma rz_size_hi : forall n, 64513 <= n -> rz_size n = 2048.
Proof.
  intros n H. unfold rz_size, rz_log.
  replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 64512) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(* the least secondary request is 64,513 (a8's YGcfSecBound.sec_req_min_exact says the same of from_primary) *)
Lemma primary_iff : forall n, is_primary n = negb (64513 <=? n).
Proof.
  intros n. unfold is_primary, needed0, rounded_size, rup, K_MAX_SIZE.
  pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as Mb.
  set (q := (Z.max n 8 + 8 - 1) / 8) in *. set (r := (Z.max n 8 + 8 - 1) mod 8) in *. clearbody q r.
  destruct (Z.leb_spec 64513 n) as [Hn|Hn]; cbn [negb].
  - rewrite (rz_size_hi n Hn). apply Z.leb_gt. lia.
  - pose proof (rz_size_lo n ltac:(lia)).
    assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_nonneg; lia).
    apply Z.leb_le. lia.
Qed.

Lemma sec_req_iff : forall n, sec_req n = (64513 <=? n).
Proof. intros n. unfold sec_req. rewrite primary_iff. apply negb_involutive. Qed.

(* the weight's threshold for the secondaries: wT = 8 * 2 ^ 8 = 2048, the first secondary kids capacity *)
Definition JT_SEC : nat := 8%nat.

(* every secondary request of the reader weighs at least 1024 *)
Lemma sec_min : forall e, ev_shape e ->
  match req_ev e with Some r => sec_req (Z.of_nat r) = true -> (1024 <= wev JT_SEC e)%nat | None => True end.
Proof.
  intros e He. destruct e as [n|m n|n|n]; cbn [req_ev]; try exact I.
  - intros H. rewrite sec_req_iff in H. apply Z.leb_le in H. cbn [wev]. lia.
  - intros H. rewrite sec_req_iff in H. apply Z.leb_le in H.
    destruct He as (j & [-> | ->]).
    + (* kids, 448 * 2 ^ j bytes: a secondary only from capacity 2048 (j >= 8) *)
      replace (448 * 2 ^ j)%nat with (56 * (8 * 2 ^ j))%nat in * by lia. rewrite wchg_kids.
      assert (Hj : (8 <= j)%nat).
      { destruct (Nat.le_gt_cases 8 j) as [Hj|Hj]; [exact Hj|].
        assert (Hp : (2 ^ j <= 2 ^ 7)%nat) by (apply Nat.pow_le_mono_r; lia).
        change (2 ^ 7)%nat with 128%nat in Hp. lia. }
      destruct (Nat.eq_dec j 8) as [->|Hne].
      * apply Nat.leb_le. vm_compute. reflexivity.
      * assert (Hq : (2 ^ 9 <= 2 ^ j)%nat) by (apply Nat.pow_le_mono_r; lia).
        change (2 ^ 9)%nat with 512%nat in Hq.
        unfold Wc, wT, JT_SEC. change (2 ^ 8)%nat with 256%nat.
        set (p := (2 ^ j)%nat) in *. clearbody p.
        destruct (Nat.ltb_spec (8 * p) (8 * 256)); [lia|].
        destruct (Nat.eqb_spec (8 * p) (8 * 256)); [lia|].
        unfold PjCharge.gchg. eqbs; dm; lia.
    + (* keys, 64 * 2 ^ j bytes: a secondary only from capacity 8192 (j >= 10) *)
      assert (Hc : capok (8 * 2 ^ j)%nat) by (right; exists j; reflexivity).
      pose proof (pow2_pos j) as Hp0.
      replace (64 * 2 ^ j)%nat with (8 * (8 * 2 ^ j))%nat in * by lia.
      rewrite (wchg_keys JT_SEC m (8 * 2 ^ j)%nat Hc ltac:(lia)).
      assert (Hj : (10 <= j)%nat).
      { destruct (Nat.le_gt_cases 10 j) as [Hj|Hj]; [exact Hj|].
        assert (Hp : (2 ^ j <= 2 ^ 9)%nat) by (apply Nat.pow_le_mono_r; lia).
        change (2 ^ 9)%nat with 512%nat in Hp. lia. }
      assert (Hq : (2 ^ 10 <= 2 ^ j)%nat) by (apply Nat.pow_le_mono_r; lia).
      change (2 ^ 10)%nat with 1024%nat in Hq.
      unfold Wc, wT, JT_SEC. change (2 ^ 8)%nat with 256%nat.
      set (p := (2 ^ j)%nat) in *. clearbody p.
      destruct (Nat.ltb_spec (8 * p) (8 * 256)); [lia|].
      destruct (Nat.eqb_spec (8 * p) (8 * 256)); [lia|].
      unfold PjCharge.gchg. eqbs; dm; lia.
Qed.

(* LSEC and its closed form are DEFINED in the leaf PresetLiveBounds.v (it keeps lib/Prog/*_c.v out of the kit's Require
   closure; do not fold it back) and re-exported here as the same terms *)
Notation LSEC_A := PresetLiveBounds.LSEC_A.
Notation LSEC_B := PresetLiveBounds.LSEC_B.
Notation LSEC := PresetLiveBounds.LSEC.
Notation LSEC_value := PresetLiveBounds.LSEC_value.

(* THE SECONDARIES: at every position of the calls, at most LSEC = 9,521 live secondary requests *)
Theorem live_sec : forall sm x os i, Z.of_nat (length x) <= MAXB ->
  Z.of_nat (cnt sec_req (hlive (firstn i (hruns sm x os)))) <= LSEC.
Proof.
  intros sm x os i Hx.
  pose proof (w_core JT_SEC sm x os sec_req 1024 (Z.to_nat 64496) 1024 Hx ltac:(lia) ltac:(lia) ltac:(lia))
    as W.
  assert (HG : forall e, ev_shape e -> is_grow e = true ->
     match req_ev e with Some r => sec_req (Z.of_nat r) = true -> (1024 <= wev JT_SEC e)%nat | None => True end)
    by (intros e He _; exact (sec_min e He)).
  assert (HS : forall e, ev_shape e -> is_grow e = false ->
     match req_ev e with Some r => sec_req (Z.of_nat r) = true -> (Z.to_nat 64496 <= chg_ev e)%nat | None => True end).
  { intros e _ Hg. destruct e as [n|m n|n|n]; cbn [req_ev is_grow] in *; try discriminate; try exact I.
    intros H. rewrite sec_req_iff in H. apply Z.leb_le in H. cbn [chg_ev]. lia. }
  specialize (W HG HS i).
  rewrite Z2Nat.id in W by lia.
  replace (Z.of_nat 1024) with 1024 in W by reflexivity.
  unfold LSEC, LSEC_A, LSEC_B. exact W.
Qed.

(* the allocator state's live secondaries: the model's plus the driver's at most 3 *)
Corollary live_sec_state : forall sm x os i (L d : list Z), Z.of_nat (length x) <= MAXB ->
  (length d <= 3)%nat -> Permutation L (hlive (firstn i (hruns sm x os)) ++ d) ->
  Z.of_nat (cnt sec_req L) <= LSEC + DRV.
Proof.
  intros sm x os i L d Hx Hd Hp. pose proof (cnt_state sec_req L _ d Hd Hp).
  pose proof (live_sec sm x os i Hx). unfold DRV. lia.
Qed.

(* h-pre-b1's side condition, Lsec + QSEC_MAX < cf_sec_live_max, at the values of the cf instance (read at
   cold/h-mani-a8-preset-alloc 107dece8291d): QSEC_MAX = (kQuarantineMax + kQuarantineCacheMax) / 64513 = 4,177
   (YGcfSecBound.QSEC_MAX / QSEC_MAX_value, the same Q_MAX + Q_CACHE = QT as PresetRoom's), cf_sec_live_max = 16,000
   (lib/A/CfParamsPreset.v, CfParams_preset's fourth argument). *)
Lemma QSEC_of_QT : QT / 64513 = 4177.
Proof. vm_compute. reflexivity. Qed.

Lemma LSEC_side : LSEC + DRV + QT / 64513 < 16000.
Proof. vm_compute. reflexivity. Qed.

(* for the record: P8's own per-event charge (the kids grow to 2048 charges 512) gives 18,737, which does not meet the
   side condition (18,737 + 3 + 4,177 > 16,000); that is why part 1 exists *)
Lemma LSEC_unweighted_value :
  3 + Z.max (3 * ((MAXB + 96) / 512)) ((MAXB + 96) / 512 + 2 * ((MAXB + 96) / 512 + (3 * MAXB + 96) / 64496 + 4) + 2)
  = 18737.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------- class 24 (5,889 .. 7,936-byte requests) *)

Definition JT_24 : nat := 4%nat.

(* class 24's grows are the kids array's grow to capacity 128 (7,168 bytes), weight K 128 = 66 *)
Lemma c24_tab : wchk_minG JT_24 (g_pcl 24) 66 g_hi 9 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lo24 : lo 24 = 5889.
Proof. vm_compute. reflexivity. Qed.

Lemma g_pcl_hi : forall c r, g_pcl c r = true -> (r <= g_hi)%nat.
Proof.
  intros c r Hr. unfold g_pcl, in_cls, cls in Hr.
  destruct (is_primary (Z.of_nat r)) eqn:Ep; [|discriminate].
  destruct r as [|r']; [lia|].
  pose proof (cls_small (Z.of_nat (S r')) ltac:(lia) Ep). pose proof g_hi_z. lia.
Qed.

(* L24 and its closed form: DEFINED in the leaf PresetLiveBounds.v, re-exported as the same terms *)
Notation L24_A := PresetLiveBounds.L24_A.
Notation L24_B := PresetLiveBounds.L24_B.
Notation L24 := PresetLiveBounds.L24.
Notation L24_value := PresetLiveBounds.L24_value.

(* CLASS 24: at every position of the calls, at most L24 = 146,219 live class-24 requests *)
Theorem live_c24 : forall sm x os i, Z.of_nat (length x) <= MAXB ->
  Z.of_nat (cnt (in_cls 24) (hlive (firstn i (hruns sm x os)))) <= L24.
Proof.
  intros sm x os i Hx.
  pose proof (w_core JT_24 sm x os (in_cls 24) 66 (Z.to_nat 5872) 66 Hx ltac:(lia) ltac:(lia) ltac:(lia))
    as W.
  assert (HG : forall e, ev_shape e -> is_grow e = true ->
     match req_ev e with Some r => in_cls 24 (Z.of_nat r) = true -> (66 <= wev JT_24 e)%nat | None => True end)
    by exact (wchk_minG_ok JT_24 (g_pcl 24) 66 g_hi 9 c24_tab (g_pcl_hi 24)).
  assert (Hm : (Z.to_nat 5872 <= Nat.max (Z.to_nat (lo 24) - 17) 1)%nat) by (rewrite lo24; lia).
  assert (HS : forall e, ev_shape e -> is_grow e = false ->
     match req_ev e with Some r => in_cls 24 (Z.of_nat r) = true -> (Z.to_nat 5872 <= chg_ev e)%nat | None => True end)
    by exact (g_minS 24 (lo 24) (Z.to_nat 5872) (lo_le 24) Hm).
  specialize (W HG HS i).
  rewrite Z2Nat.id in W by lia.
  replace (Z.of_nat 66) with 66 in W by reflexivity.
  unfold L24, L24_A, L24_B. exact W.
Qed.

Corollary live_c24_state : forall sm x os i (L d : list Z), Z.of_nat (length x) <= MAXB ->
  (length d <= 3)%nat -> Permutation L (hlive (firstn i (hruns sm x os)) ++ d) ->
  Z.of_nat (cnt (in_cls 24) L) <= L24 + DRV.
Proof.
  intros sm x os i L d Hx Hd Hp. pose proof (cnt_state (in_cls 24) L _ d Hd Hp).
  pose proof (live_c24 sm x os i Hx). unfold DRV. lia.
Qed.

(* NON-VACUITY: the premises of live_sec_state / live_c24_state hold, for every call list and position and every input
   length up to MAXB (the input of n spaces, the model's own live list, no driver block). The theorems take no Section
   hypothesis: their only premises are the ones stated. *)
Lemma live_premises_hold : forall sm os i (n : nat), Z.of_nat n <= MAXB ->
  exists x L d, length x = n /\ Z.of_nat (length x) <= MAXB /\ (length d <= 3)%nat /\
  Permutation L (hlive (firstn i (hruns sm x os)) ++ d).
Proof.
  intros sm os i n Hn. exists (repeat 32 n), (hlive (firstn i (hruns sm (repeat 32 n) os)) ++ []), [].
  rewrite repeat_length. split; [reflexivity|]. split; [exact Hn|]. split; [cbn; lia|]. apply Permutation_refl.
Qed.

(* class 24 is the batch class (PresetRoom.K_BATCH_CLASS): L24 + DRV live, the quarantine's most class-24 chunks,
   its most batch records and the refill fit the class's slots (room_ok; 224,817 of cap 24 = 458,752) *)
Lemma L24_room : room_ok 24 (L24 + DRV).
Proof. unfold room_ok. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma L24_room_value : L24 + DRV + QT / (lo 24 + 8) + QT / Q_BATCH_BYTES + refill 24 = 224817 /\ cap 24 = 458752.
Proof. split; vm_compute; reflexivity. Qed.

(* for the record: PresetGate.g_core at c = 24 with P8's own charges (m_G = g_mG 24 = 32) gives 298,148 *)
Lemma L24_unweighted_value :
  3 + Z.max (3 * ((MAXB + 96) / 32)) ((MAXB + 96) / 32 + 2 * ((MAXB + 96) / 32 + (3 * MAXB + 96) / 5872 + 4) + 2)
  = 298148.
Proof. vm_compute. reflexivity. Qed.
