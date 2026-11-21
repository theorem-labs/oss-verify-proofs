(** * EnoughFitsB1 — B-cluster session 1: the abstraction layer, the
    DP recurrence, and the it_step anatomy (g6-bound lane).

    ARCHITECTURE AMENDMENT (Tier-B, amendable class; NOTED per the
    session terms): the invariant's i2 conjunct moves from
    [dp_peak] (the MEMOIZED oracle walker) to [dp_max] (the pristine
    max-recursion defined here).  Rationale: the model-side invariant
    then never touches the done-set; memoization soundness
    ([dp_max <= the oracle's walked value]) is needed ONCE, at the
    seed, instead of at every step.  The recurrence on [dp_max] is
    structural and proven below; the seed-soundness obligation is the
    named Section target [dpmax_seed_sound_STMT].

    f1 COMPLIANCE: the opening's sizing is wrapped once as
    [open_curr] (opaque-by-name; unfold on demand); no raw it_subsz
    equation is ever placed in a context.  All lias need-set
    clear-guarded, no backtracking fallbacks. *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblGeom.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The pristine DP maximum [dp_max] — examineF's search WITHOUT the
       memo/large threading, with a NAMED loop (dpm_loop) whose
       accounting step IS [chain_code] (EnoughFitsDesign), so the
       chain-replay abstractions align by construction.
   ========================================================================== *)

Definition dpm_least (syms left : Z) : Z := Z.max 0 (2 * left - syms).
Definition dpm_most (mx syms left len : Z) : Z :=
  (left * 2 ^ (mx - len) - syms) / (2 ^ (mx - len) - 1).

Fixpoint dpm_loop (child : Z -> Z -> Z -> Z) (subsz : Z)
                  (n : nat) (use mem rem acc : Z) : Z :=
  match n with
  | O => acc
  | S n' =>
      let c := child use mem rem in
      let '(mem', rem') := chain_code subsz mem rem in
      dpm_loop child subsz n' (use + 1) mem' rem' (Z.max acc c)
  end.

Fixpoint dp_max (f : nat) (mx rt syms left len mem rem : Z) : Z :=
  match f with
  | O => 0
  | S f' =>
      let subsz := 2 ^ (len - rt) in
      if syms =? left then
        let '(_, mem1, _) :=
          drain (Z.to_nat left + 2)%nat subsz left mem rem in
        mem1
      else
        let '(use1, mem1, rem1) :=
          drain (Z.to_nat (dpm_least syms left) + 2)%nat subsz
                (dpm_least syms left) mem rem in
        dpm_loop
          (fun use m r =>
             dp_max f' mx rt (syms - use) (2 * (left - use)) (len + 1)
               (m + (if r =? 0 then 0 else subsz)) (2 * r))
          subsz
          (Z.to_nat (dpm_most mx syms left len - dpm_least syms left + 1))
          (dpm_least syms left) mem1 (rem1 - use1) 0
  end.

(** ** The recurrence lemmas *)

Lemma dpm_loop_acc_le : forall child subsz n use mem rem acc,
  acc <= dpm_loop child subsz n use mem rem acc.
Proof.
  intros child subsz n.
  induction n as [|n IH]; intros use mem rem acc; cbn [dpm_loop].
  - clear; lia.
  - destruct (chain_code subsz mem rem) as [mem' rem'].
    eapply Z.le_trans; [|apply IH].
    pose proof (Z.le_max_l acc (child use mem rem)). clear -H; lia.
Qed.

Lemma dpm_loop_child_le : forall child subsz n j use mem rem acc,
  (j < n)%nat ->
  child (use + Z.of_nat j) (fst (chain_codes j subsz mem rem))
        (snd (chain_codes j subsz mem rem))
    <= dpm_loop child subsz n use mem rem acc.
Proof.
  intros child subsz n.
  induction n as [|n IH]; intros j use mem rem acc Hj.
  - exfalso. clear -Hj; lia.
  - cbn [dpm_loop].
    destruct (chain_code subsz mem rem) as [mem' rem'] eqn:EC.
    destruct j as [|j'].
    + cbn [chain_codes fst snd].
      rewrite Z.add_0_r.
      eapply Z.le_trans; [|apply dpm_loop_acc_le].
      pose proof (Z.le_max_r acc (child use mem rem)). clear -H; lia.
    + cbn [chain_codes]. rewrite EC.
      replace (use + Z.of_nat (S j')) with ((use + 1) + Z.of_nat j')
        by (rewrite Nat2Z.inj_succ; clear; lia).
      apply IH. clear -Hj; lia.
Qed.

(** The complete-node value. *)
Lemma dp_max_complete : forall f mx rt syms left len mem rem u m1 r1,
  (syms =? left) = true ->
  drain (Z.to_nat left + 2)%nat (2 ^ (len - rt)) left mem rem
    = (u, m1, r1) ->
  dp_max (S f) mx rt syms left len mem rem = m1.
Proof.
  intros f mx rt syms left len mem rem u m1 r1 Hc Hd.
  cbn [dp_max]. rewrite Hc, Hd. reflexivity.
Qed.

(** The child-domination recurrence: at a non-complete node, every
    use-loop position's child value is <= the node's dp_max.  The
    position's accounting is [chain_codes] after the least-drain —
    exactly the replay the invariant carries. *)
Lemma dp_max_child_le : forall f mx rt syms left len mem rem u1 m1 r1 j,
  (syms =? left) = false ->
  drain (Z.to_nat (dpm_least syms left) + 2)%nat (2 ^ (len - rt))
        (dpm_least syms left) mem rem = (u1, m1, r1) ->
  (j < Z.to_nat (dpm_most mx syms left len - dpm_least syms left + 1))%nat ->
  dp_max f mx rt
    (syms - (dpm_least syms left + Z.of_nat j))
    (2 * (left - (dpm_least syms left + Z.of_nat j)))
    (len + 1)
    (fst (chain_codes j (2 ^ (len - rt)) m1 (r1 - u1))
       + (if snd (chain_codes j (2 ^ (len - rt)) m1 (r1 - u1)) =? 0
          then 0 else 2 ^ (len - rt)))
    (2 * snd (chain_codes j (2 ^ (len - rt)) m1 (r1 - u1)))
  <= dp_max (S f) mx rt syms left len mem rem.
Proof.
  intros f mx rt syms left len mem rem u1 m1 r1 j Hc Hd Hj.
  cbn [dp_max]. rewrite Hc, Hd.
  exact (dpm_loop_child_le
           (fun use m r =>
              dp_max f mx rt (syms - use) (2 * (left - use)) (len + 1)
                (m + (if r =? 0 then 0 else 2 ^ (len - rt))) (2 * r))
           (2 ^ (len - rt)) _ j (dpm_least syms left) m1 (r1 - u1) 0 Hj).
Qed.

(* ==========================================================================
   2.  The it_step ANATOMY — branch-indexed equations the step lemmas
       destructure over.  [open_curr] is the f1 wrapper: the ONLY name
       under which the opening's it_subsz sizing may enter a context.
   ========================================================================== *)

Definition step_incr (st : ItSt) : Z := Z.shiftl 1 (s_len st - s_drop st).
Definition step_fill0 (st : ItSt) : Z := Z.shiftl 1 (s_curr st).
Definition step_tbl (c : ItCtx) (st : ItSt) : ztbl :=
  it_fill (Z.to_nat (step_fill0 st / step_incr st)) (s_tbl st)
          (s_next st + Z.shiftr (s_huff st) (s_drop st)) (step_incr st)
          (it_here c st).
Definition step_huff (st : ItSt) : Z := it_rev_incr (s_huff st) (s_len st).
Definition step_cnt (st : ItSt) : zarr :=
  zset (s_count st) (s_len st) (s_count st (s_len st) - 1).
Definition step_hit (st : ItSt) : bool := step_cnt st (s_len st) =? 0.
Definition step_len (c : ItCtx) (st : ItSt) : Z :=
  if step_hit st then x_lens c (x_work c (s_sym st + 1)) else s_len st.

(** The post-fill base state (the C's state after :218-240, before any
    sub-table decision) — shared by every non-overflow outcome. *)
Definition step_base (c : ItCtx) (st : ItSt) : ItSt :=
  {| s_huff := step_huff st; s_sym := s_sym st + 1; s_len := s_len st;
     s_next := s_next st; s_curr := s_curr st; s_drop := s_drop st;
     s_low := s_low st; s_used := s_used st; s_min := step_fill0 st;
     s_count := step_cnt st; s_tbl := step_tbl c st |}.

Definition open_guard (c : ItCtx) (st : ItSt) : bool :=
  (x_root c <? step_len c st)
  && negb (Z.land (step_huff st) (x_mask c) =? s_low st).

Definition open_drop (c : ItCtx) (st : ItSt) : Z :=
  if s_drop st =? 0 then x_root c else s_drop st.

(** f1 WRAPPER: the opening's lookahead size.  Contexts carry facts
    about [open_curr c st], never a raw it_subsz application. *)
Definition open_curr (c : ItCtx) (st : ItSt) : Z :=
  it_subsz 16%nat (step_cnt st) (open_drop c st) (x_max c)
           (step_len c st - open_drop c st)
           (Z.shiftl 1 (step_len c st - open_drop c st)).

Definition open_used (c : ItCtx) (st : ItSt) : Z :=
  s_used st + Z.shiftl 1 (open_curr c st).

Definition step_open_st (c : ItCtx) (st : ItSt) : ItSt :=
  {| s_huff := step_huff st; s_sym := s_sym st + 1;
     s_len := step_len c st;
     s_next := s_next st + step_fill0 st;
     s_curr := open_curr c st; s_drop := open_drop c st;
     s_low := Z.land (step_huff st) (x_mask c);
     s_used := open_used c st; s_min := step_fill0 st;
     s_count := step_cnt st;
     s_tbl := tset (step_tbl c st) (Z.land (step_huff st) (x_mask c))
                   (mkCodeT (open_curr c st) (x_root c)
                            (s_next st + step_fill0 st)) |}.

Definition step_noopen_st (c : ItCtx) (st : ItSt) : ItSt :=
  {| s_huff := step_huff st; s_sym := s_sym st + 1;
     s_len := step_len c st;
     s_next := s_next st; s_curr := s_curr st; s_drop := s_drop st;
     s_low := s_low st; s_used := s_used st; s_min := step_fill0 st;
     s_count := step_cnt st; s_tbl := step_tbl c st |}.

Lemma it_step_break_eq : forall c st,
  step_hit st = true -> (s_len st =? x_max c) = true ->
  it_step c st = ItBreak (step_base c st).
Proof.
  intros c st Hh Hm.
  unfold it_step. cbv zeta.
  cbv [step_base step_huff step_fill0 step_cnt step_tbl
       step_incr step_hit] in *.
  rewrite Hh, Hm. cbn [andb]. cbv iota. reflexivity.
Qed.

Lemma it_step_overflow_eq : forall c st,
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  it_enough (x_type c) (open_used c st) = true ->
  it_step c st = ItOverflow (step_tbl c st).
Proof.
  intros c st Hbrk Hop Hen.
  unfold it_step. cbv zeta.
  cbv [open_guard open_used open_curr open_drop step_len
       step_hit step_cnt step_huff step_fill0 step_tbl
       step_incr] in *.
  rewrite Hbrk. cbv iota.
  rewrite Hop. cbv iota.
  rewrite Hen. cbv iota.
  reflexivity.
Qed.

Lemma it_step_opencont_eq : forall c st,
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  it_enough (x_type c) (open_used c st) = false ->
  it_step c st = ItCont (step_open_st c st).
Proof.
  intros c st Hbrk Hop Hen.
  unfold it_step. cbv zeta.
  cbv [step_open_st open_guard open_used open_curr open_drop
       step_len step_hit step_cnt step_huff step_fill0 step_tbl
       step_incr] in *.
  rewrite Hbrk. cbv iota.
  rewrite Hop. cbv iota.
  rewrite Hen. cbv iota.
  reflexivity.
Qed.

Lemma it_step_noopen_eq : forall c st,
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = false ->
  it_step c st = ItCont (step_noopen_st c st).
Proof.
  intros c st Hbrk Hop.
  unfold it_step. cbv zeta.
  cbv [step_noopen_st open_guard step_len step_hit step_cnt
       step_huff step_fill0 step_tbl step_incr] in *.
  rewrite Hbrk. cbv iota.
  rewrite Hop. cbv iota.
  reflexivity.
Qed.

(** The overflow characterization B4 refutes: an overflow step IS an
    opening whose lookahead charge trips the guard. *)
Lemma it_step_overflow_inv : forall c st t,
  it_step c st = ItOverflow t ->
  (step_hit st && (s_len st =? x_max c))%bool = false
  /\ open_guard c st = true
  /\ it_enough (x_type c) (open_used c st) = true
  /\ t = step_tbl c st.
Proof.
  intros c st t H.
  destruct ((step_hit st && (s_len st =? x_max c))%bool) eqn:Hbrk.
  { apply andb_true_iff in Hbrk. destruct Hbrk as [Hh Hm].
    rewrite (it_step_break_eq c st Hh Hm) in H. discriminate H. }
  destruct (open_guard c st) eqn:Hop.
  - destruct (it_enough (x_type c) (open_used c st)) eqn:Hen.
    + rewrite (it_step_overflow_eq c st Hbrk Hop Hen) in H.
      injection H as ->.
      repeat split; reflexivity.
    + rewrite (it_step_opencont_eq c st Hbrk Hop Hen) in H.
      discriminate H.
  - rewrite (it_step_noopen_eq c st Hbrk Hop) in H. discriminate H.
Qed.

(* ==========================================================================
   3.  key5 injectivity on the guarded domain (memoization-soundness
       scaffold) + the domain predicate.
   ========================================================================== *)

Definition dom5 (syms left len mem rem : Z) : Prop :=
  0 <= syms < W /\ 0 <= left < W /\ 0 <= len < W
  /\ 0 <= mem < W /\ 0 <= rem < W.

Lemma mixed_radix_split : forall a b x y,
  0 <= a < W -> 0 <= b < W ->
  a + W * x = b + W * y ->
  a = b /\ x = y.
Proof.
  intros a b x y Ha Hb He.
  assert (HW : 0 < W) by (unfold W; clear; lia).
  destruct (Z.lt_trichotomy x y) as [Hlt|[Heq|Hgt]].
  - exfalso.
    assert (Hd : W * (y - x) = a - b) by (clear -He; lia).
    assert (H1 : 1 <= y - x) by (clear -Hlt; lia).
    assert (H2 : W * 1 <= W * (y - x))
      by (apply Z.mul_le_mono_nonneg_l; clear -H1 HW; lia).
    clear -Hd H2 Ha Hb HW; lia.
  - subst y. split; [clear -He; lia | reflexivity].
  - exfalso.
    assert (Hd : W * (x - y) = b - a) by (clear -He; lia).
    assert (H1 : 1 <= x - y) by (clear -Hgt; lia).
    assert (H2 : W * 1 <= W * (x - y))
      by (apply Z.mul_le_mono_nonneg_l; clear -H1 HW; lia).
    clear -Hd H2 Ha Hb HW; lia.
Qed.

Lemma key5_inj : forall s1 l1 L1 m1 r1 s2 l2 L2 m2 r2,
  dom5 s1 l1 L1 m1 r1 -> dom5 s2 l2 L2 m2 r2 ->
  key5 s1 l1 L1 m1 r1 = key5 s2 l2 L2 m2 r2 ->
  s1 = s2 /\ l1 = l2 /\ L1 = L2 /\ m1 = m2 /\ r1 = r2.
Proof.
  intros s1 l1 L1 m1 r1 s2 l2 L2 m2 r2 D1 D2 He.
  unfold dom5 in D1, D2.
  destruct D1 as (Hs1 & Hl1 & HL1 & Hm1 & Hr1).
  destruct D2 as (Hs2 & Hl2 & HL2 & Hm2 & Hr2).
  assert (HW : 0 < W) by (unfold W; clear; lia).
  unfold key5 in He.
  (* strip Z.to_pos: both arguments are >= 1 *)
  assert (HP1 : 0 < 1 + r1 + W * (m1 + W * (L1 + W * (l1 + W * s1)))).
  { assert (0 <= m1 + W * (L1 + W * (l1 + W * s1)))
      by (apply Z.add_nonneg_nonneg;
          [clear -Hm1; lia
          | apply Z.mul_nonneg_nonneg;
            [clear -HW; lia
            | apply Z.add_nonneg_nonneg;
              [clear -HL1; lia
              | apply Z.mul_nonneg_nonneg;
                [clear -HW; lia
                | apply Z.add_nonneg_nonneg;
                  [clear -Hl1; lia
                  | apply Z.mul_nonneg_nonneg; clear -HW Hs1; lia]]]]]).
    assert (0 <= W * (m1 + W * (L1 + W * (l1 + W * s1))))
      by (apply Z.mul_nonneg_nonneg; clear -HW H; lia).
    clear -Hr1 H0; lia. }
  assert (HP2 : 0 < 1 + r2 + W * (m2 + W * (L2 + W * (l2 + W * s2)))).
  { assert (0 <= m2 + W * (L2 + W * (l2 + W * s2)))
      by (apply Z.add_nonneg_nonneg;
          [clear -Hm2; lia
          | apply Z.mul_nonneg_nonneg;
            [clear -HW; lia
            | apply Z.add_nonneg_nonneg;
              [clear -HL2; lia
              | apply Z.mul_nonneg_nonneg;
                [clear -HW; lia
                | apply Z.add_nonneg_nonneg;
                  [clear -Hl2; lia
                  | apply Z.mul_nonneg_nonneg; clear -HW Hs2; lia]]]]]).
    assert (0 <= W * (m2 + W * (L2 + W * (l2 + W * s2))))
      by (apply Z.mul_nonneg_nonneg; clear -HW H; lia).
    clear -Hr2 H0; lia. }
  apply Z2Pos.inj in He; [|exact HP1|exact HP2].
  (* peel the radix layers *)
  assert (He1 : r1 + W * (m1 + W * (L1 + W * (l1 + W * s1)))
              = r2 + W * (m2 + W * (L2 + W * (l2 + W * s2))))
    by (clear -He; lia).
  destruct (mixed_radix_split _ _ _ _
              (conj (proj1 Hr1) (proj2 Hr1))
              (conj (proj1 Hr2) (proj2 Hr2)) He1) as [Er He2].
  destruct (mixed_radix_split _ _ _ _
              (conj (proj1 Hm1) (proj2 Hm1))
              (conj (proj1 Hm2) (proj2 Hm2)) He2) as [Em He3].
  destruct (mixed_radix_split _ _ _ _
              (conj (proj1 HL1) (proj2 HL1))
              (conj (proj1 HL2) (proj2 HL2)) He3) as [EL He4].
  destruct (mixed_radix_split _ _ _ _
              (conj (proj1 Hl1) (proj2 Hl1))
              (conj (proj1 Hl2) (proj2 Hl2)) He4) as [El He5].
  assert (Es : s1 = s2) by (clear -He5; lia).
  repeat split; assumption.
Qed.

(* ==========================================================================
   4.  The amended invariant conjunct target + the seed-soundness
       obligation (Section-hypothesis form; the B-cluster's remaining
       oracle-side wall, localized to ONE application at the seed).
   ========================================================================== *)

(** i2', the dp_max form (replaces the design's dp_peak form —
    Tier-B amendment, noted in the session report). *)
Definition i2' (ty mx rt syms left len mem rem : Z) : Prop :=
  dp_max (S (Z.to_nat mx)) mx rt syms left len mem rem
    <= (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS).

(** Seed soundness: the pristine maximum from every juncture
    enough_phase walks is <= the oracle's computed bound.  ONE
    obligation, discharged in a later session via the SoundBelow
    machinery (key5_inj above is its arithmetic core). *)
Definition dpmax_seed_sound_STMT : Prop :=
  forall syms root max large,
    enough_bound syms root max = Some large ->
    forall n left,
      3 <= n <= syms -> 2 <= left < n ->
      (* the two seed shapes enough_phase examines (enough.c:466-474) *)
      dp_max (S (Z.to_nat (Z.min max (syms - 1))))
             (Z.min max (syms - 1)) (Z.min root (Z.min max (syms - 1)))
             n left (Z.min root (Z.min max (syms - 1)) + 1)
             (2 ^ Z.min root (Z.min max (syms - 1))) 0
        <= large.
