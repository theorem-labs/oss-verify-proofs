(** * EnoughFitsB2 — B-cluster session 2: chain accounting laws, the
    it_subsz window spec, the AJ overlay invariant (riding the landed
    SubLedger/CovInv), and the no-open preservation (g6-bound lane).

    DEBT VERDICT (headline, DESIGN.md §9): the EQUATION form of i3
    SURVIVES on the session's evidence — the open-trip matching reduces
    to "crossings happen only at full lookahead depth", carried by
    SubLedger's landed guard clause + the it_subsz window fold ((s3),
    stated here, Qed'd next session).  f2 unused; route B unused.

    f1: open_curr remains the only it_subsz carrier; the window spec is
    stated ABOUT open_curr/it_subsz, consumed by name. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblGeom ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Chain accounting laws.
   ========================================================================== *)

Lemma chain_code_mem_mono : forall subsz mem rem,
  0 <= subsz ->
  mem <= fst (chain_code subsz mem rem).
Proof.
  intros subsz mem rem Hs. unfold chain_code.
  destruct (rem =? 0); cbn [fst]; clear -Hs; lia.
Qed.

Lemma chain_codes_mem_mono : forall k subsz mem rem,
  0 <= subsz ->
  mem <= fst (chain_codes k subsz mem rem).
Proof.
  induction k as [|k IH]; intros subsz mem rem Hs; cbn [chain_codes fst].
  - clear; lia.
  - destruct (chain_code subsz mem rem) as [m' r'] eqn:EC.
    eapply Z.le_trans; [|apply IH; exact Hs].
    pose proof (chain_code_mem_mono subsz mem rem Hs) as HM.
    rewrite EC in HM. cbn [fst] in HM. exact HM.
Qed.

Lemma chain_codes_tail : forall k s m r,
  chain_codes (S k) s m r
  = chain_code s (fst (chain_codes k s m r)) (snd (chain_codes k s m r)).
Proof.
  induction k as [|k IH]; intros s m r.
  - cbn [chain_codes fst snd].
    destruct (chain_code s m r) as [a b]. reflexivity.
  - change (chain_codes (S (S k)) s m r) with
      (let '(a, b) := chain_code s m r in chain_codes (S k) s a b).
    change (chain_codes (S k) s m r) with
      (let '(a, b) := chain_code s m r in chain_codes k s a b).
    destruct (chain_code s m r) as [a b].
    apply IH.
Qed.

Lemma chain_descend_mem_mono : forall subsz mem rem,
  0 <= subsz ->
  mem <= fst (chain_descend subsz mem rem).
Proof.
  intros subsz mem rem Hs. unfold chain_descend. cbn [fst].
  destruct (rem =? 0); clear -Hs; lia.
Qed.

(** Tail-unfold of the boundary replay: the accounting at [l + 1] is one
    length-block (codes then descend) past the accounting at [l]. *)
Lemma chain_at_aux_tail : forall n cnt rt l mem rem,
  chain_at_aux (S n) cnt rt l mem rem
  = (let subsz := 2 ^ (l + Z.of_nat n - rt) in
     let '(m1, r1) := chain_codes (Z.to_nat (cnt (l + Z.of_nat n))) subsz
                        (fst (chain_at_aux n cnt rt l mem rem))
                        (snd (chain_at_aux n cnt rt l mem rem)) in
     chain_descend subsz m1 r1).
Proof.
  induction n as [|n IH]; intros cnt rt l mem rem.
  - cbn [chain_at_aux]. cbv zeta.
    rewrite Z.add_0_r.
    destruct (chain_codes (Z.to_nat (cnt l)) (2 ^ (l - rt)) mem rem)
      as [m1 r1] eqn:E1.
    cbn [fst snd].
    rewrite E1.
    destruct (chain_descend (2 ^ (l - rt)) m1 r1) as [m2 r2] eqn:E2.
    cbn [chain_at_aux]. reflexivity.
  - cbn [chain_at_aux] in *. cbv zeta in *.
    destruct (chain_codes (Z.to_nat (cnt l)) (2 ^ (l - rt)) mem rem)
      as [m1 r1] eqn:E1.
    destruct (chain_descend (2 ^ (l - rt)) m1 r1) as [m2 r2] eqn:E2.
    rewrite (IH cnt rt (l + 1) m2 r2).
    replace (l + 1 + Z.of_nat n) with (l + Z.of_nat (S n))
      by (rewrite Nat2Z.inj_succ; clear; lia).
    reflexivity.
Qed.

(** One-length unfold of [chain_at] at the boundary form. *)
Lemma chain_at_step : forall cnt rt l,
  rt + 1 <= l ->
  chain_at cnt rt (l + 1)
  = (let subsz := 2 ^ (l - rt) in
     let '(m1, r1) := chain_codes (Z.to_nat (cnt l)) subsz
                        (fst (chain_at cnt rt l))
                        (snd (chain_at cnt rt l)) in
     chain_descend subsz m1 r1).
Proof.
  intros cnt rt l Hl. unfold chain_at.
  replace (Z.to_nat (l + 1 - rt - 1)) with (S (Z.to_nat (l - rt - 1)))
    by (clear -Hl; lia).
  rewrite chain_at_aux_tail.
  replace (rt + 1 + Z.of_nat (Z.to_nat (l - rt - 1))) with l
    by (rewrite Z2Nat.id by (clear -Hl; lia); clear; lia).
  reflexivity.
Qed.

Lemma chain_at_seed : forall cnt rt l,
  l <= rt + 1 ->
  chain_at cnt rt l = (2 ^ rt, 0).
Proof.
  intros cnt rt l Hl. unfold chain_at.
  replace (Z.to_nat (l - rt - 1)) with O by (clear -Hl; lia).
  reflexivity.
Qed.

Lemma chain_at_mem_nonneg_mono : forall cnt rt lo hi,
  rt + 1 <= lo <= hi ->
  (forall j, 0 <= cnt j) ->
  fst (chain_at cnt rt lo) <= fst (chain_at cnt rt hi).
Proof.
  intros cnt rt lo hi [Hlo Hhi] Hnn.
  replace hi with (lo + Z.of_nat (Z.to_nat (hi - lo)))
    by (rewrite Z2Nat.id by (clear -Hhi; lia); clear; lia).
  induction (Z.to_nat (hi - lo)) as [|n IH].
  - rewrite Z.add_0_r. clear; lia.
  - replace (lo + Z.of_nat (S n)) with ((lo + Z.of_nat n) + 1)
      by (rewrite Nat2Z.inj_succ; clear; lia).
    rewrite chain_at_step by (clear -Hlo; lia).
    cbv zeta.
    set (SB := 2 ^ (lo + Z.of_nat n - rt)).
    assert (HSB : 0 <= SB)
      by (unfold SB; apply Z.pow_nonneg; clear; lia).
    destruct (chain_codes (Z.to_nat (cnt (lo + Z.of_nat n))) SB
                (fst (chain_at cnt rt (lo + Z.of_nat n)))
                (snd (chain_at cnt rt (lo + Z.of_nat n))))
      as [m1 r1] eqn:E1.
    pose proof (chain_codes_mem_mono (Z.to_nat (cnt (lo + Z.of_nat n))) SB
                  (fst (chain_at cnt rt (lo + Z.of_nat n)))
                  (snd (chain_at cnt rt (lo + Z.of_nat n))) HSB) as HM1.
    rewrite E1 in HM1. cbn [fst] in HM1.
    pose proof (chain_descend_mem_mono SB m1 r1 HSB) as HM2.
    clear -IH HM1 HM2; lia.
Qed.

(* ==========================================================================
   2.  The it_subsz window spec.  (s1)/(s2) Qed; (s3) stated.
   ========================================================================== *)

Lemma it_subsz_ge : forall n cnt drop mx curr left,
  curr <= it_subsz n cnt drop mx curr left.
Proof.
  induction n as [|k IH]; intros cnt drop mx curr left; cbn [it_subsz].
  - clear; lia.
  - destruct (Z.ltb (curr + drop) mx); [|clear; lia].
    destruct (Z.leb (left - cnt (curr + drop)) 0); [clear; lia|].
    eapply Z.le_trans; [|apply IH]. clear; lia.
Qed.

Lemma it_subsz_le : forall n cnt drop mx curr left,
  it_subsz n cnt drop mx curr left <= Z.max curr (mx - drop).
Proof.
  induction n as [|k IH]; intros cnt drop mx curr left;
    cbn [it_subsz].
  - pose proof (Z.le_max_l curr (mx - drop)). clear -H; lia.
  - destruct (Z.ltb_spec (curr + drop) mx) as [Hlt|Hge].
    + destruct (Z.leb (left - cnt (curr + drop)) 0).
      * pose proof (Z.le_max_l curr (mx - drop)). clear -H; lia.
      * eapply Z.le_trans; [apply IH|].
        assert (Hc1 : curr + 1 <= mx - drop) by (clear -Hlt; lia).
        rewrite (Z.max_r (curr + 1) (mx - drop)) by (clear -Hc1; lia).
        pose proof (Z.le_max_r curr (mx - drop)). clear -H; lia.
    + pose proof (Z.le_max_l curr (mx - drop)). clear -H; lia.
Qed.

(** The explicit window fold: the [left] value after [j] extensions. *)
Fixpoint szfold (cnt : zarr) (drop curr0 : Z) (left0 : Z) (j : nat) : Z :=
  match j with
  | O => left0
  | S j' => (szfold cnt drop curr0 left0 j'
             - cnt (curr0 + Z.of_nat j' + drop)) * 2
  end.

(** (s3) — THE WINDOW LEMMA (stated; session-3 head).  If the lookahead
    returned r > curr0, then at every intermediate extension the fold
    stays positive (the table is not yet fillable), and the extension
    count is exactly r - curr0.  The crossing-fullness argument (DESIGN
    §9) consumes the positivity together with SubLedger's guard. *)
Definition it_subsz_window_STMT : Prop :=
  forall n cnt drop mx curr0 left0,
    left0 = Z.shiftl 1 curr0 ->
    (forall j, 0 <= cnt j) ->
    mx - (curr0 + drop) <= Z.of_nat n ->
    let r := it_subsz n cnt drop mx curr0 left0 in
    forall j, (Z.of_nat j < r - curr0) ->
      0 < szfold cnt drop curr0 left0 (S j).

(* ==========================================================================
   3.  The AJ overlay (i1-focus), phase-dichotomous, riding SubLedger.
   ========================================================================== *)

(** The un-descended part of the current sub-table's upfront charge. *)
Definition dbt (st : ItSt) : Z :=
  if s_drop st =? 0 then 0
  else 2 ^ s_curr st - 2 ^ (s_len st - s_drop st).

(** The DP-side accounting at the model state: boundary replay at the
    current length, then the within-length position.  [k] is read off
    CovInv's count dispatch (cnt0 len - s_count len). *)
Definition aj_acct (cnt0 : zarr) (R0 : Z) (st : ItSt) : Z * Z :=
  let len := s_len st in
  let k := Z.to_nat (cnt0 len - s_count st len) in
  chain_codes k (2 ^ (len - R0))
    (fst (chain_at cnt0 R0 len)) (snd (chain_at cnt0 R0 len)).

Definition AJ (cnt0 : zarr) (R0 : Z) (st : ItSt) : Prop :=
  s_used st <= fst (aj_acct cnt0 R0 st) + dbt st.

(* ==========================================================================
   4.  No-open, no-hit preservation of AJ (Qed).  The hit-trip and the
       open-trip preservations consume (s3) + SubLedger's guard clause
       and are STATED here (session-3 targets), with the step anatomy
       already fixing their shapes.
   ========================================================================== *)

(** A no-open trip that stays at the same length: the position advances
    one code; the DP accounting is monotone; used/dbt unchanged. *)
Lemma aj_noopen_nohit : forall cnt0 R0 c st,
  0 <= R0 ->
  AJ cnt0 R0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = false ->
  step_hit st = false ->
  s_count st (s_len st) <= cnt0 (s_len st) ->
  AJ cnt0 R0 (step_noopen_st c st).
Proof.
  intros cnt0 R0 c st HR0 HAJ Hbrk Hop Hhit Hk.
  unfold AJ, aj_acct, dbt in *. cbv zeta in *.
  cbn [step_noopen_st s_used s_len s_count s_curr s_drop] in *.
  unfold step_len. rewrite Hhit. cbv iota.
  unfold step_cnt. rewrite zset_same.
  set (SB := 2 ^ (s_len st - R0)) in *.
  assert (HSB : 0 <= SB) by (unfold SB; apply Z.pow_nonneg; clear; lia).
  set (B := chain_at cnt0 R0 (s_len st)) in *.
  replace (Z.to_nat (cnt0 (s_len st) - (s_count st (s_len st) - 1)))
    with (S (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st))))
    by (clear -Hk; lia).
  rewrite chain_codes_tail.
  set (CK := chain_codes (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
               SB (fst B) (snd B)) in *.
  pose proof (chain_code_mem_mono SB (fst CK) (snd CK) HSB) as HM.
  destruct (s_drop st =? 0); clear -HAJ HM; lia.
Qed.

(** Session-3 targets, shaped for it_step_overflow_inv's refutation:

    (T1) hit-trip preservation (len advances across a zero-count gap;
         the DP pays one doubling per level while the debt shrinks by
         the same telescoping sum — consumes (s3) + SubLedger's guard
         for rem <> 0 at each intermediate descend).
    (T2) open-trip preservation (crossing at full depth: dbt = 0 at
         the crossing by (s3)+guard, the new sub-table's charge enters
         both sides — the accounting matches with the new dbt).
    (T3) the guard refutation: AJ + SubLedger + CovInv at an opening
         imply open_used c st <= EN ty, contradicting a tripped
         it_enough via it_step_overflow_inv. *)
Definition aj_hit_STMT : Prop :=
  forall ty cnt0 R0 c st,
    x_root c = R0 -> x_type c = ty ->
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ cnt0 R0 st ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = false ->
    step_hit st = true ->
    AJ cnt0 R0 (step_noopen_st c st).

Definition aj_open_STMT : Prop :=
  forall ty cnt0 R0 c st,
    x_root c = R0 -> x_type c = ty ->
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ cnt0 R0 st ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    it_enough (x_type c) (open_used c st) = false ->
    AJ cnt0 R0 (step_open_st c st).

Definition aj_guard_STMT : Prop :=
  forall ty cnt0 R0 c st,
    x_root c = R0 -> x_type c = ty ->
    (ty = CT_LENS \/ ty = CT_DISTS) ->
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ cnt0 R0 st ->
    i2' ty (x_max c) R0
      (rem_syms cnt0 (s_len st) (x_max c))
      (kleft cnt0 (s_len st)) (s_len st)
      (fst (aj_acct cnt0 R0 st)) (snd (aj_acct cnt0 R0 st)) ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    it_enough (x_type c) (open_used c st) = false.
