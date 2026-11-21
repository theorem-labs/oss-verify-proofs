(** * EnoughFitsDesign — the ENOUGHFITS bridge-lemma STATEMENT PACK
    (g6-bound lane, TL full commission, DESIGN STAGE for a5's fit-check).

    FROZEN TARGET: EnoughFits_STMT, Gap7Strict.v:356-370 at md5
    (g1's packet; restated VERBATIM
    below — this file never mints a respell; the repair finding goes
    back through g1+q6).

    HEADLINE FINDING (machine-checked, [stmt_falsifier] below):
    EnoughFits_STMT as frozen is FALSE.  The band carries no cap on the
    ENTRIES of [l], and uncapped lengths are invisible to it_kraft's
    [1..15] window but NOT to [it_sort]: a length-47 entry writes
    through [offs 47 = 0] (zarr default — it_offs never touches index
    47) into the LOW work slots, clobbering sorted symbols.  Witness
    [1;2;2;47;47] at the LENS band: kraft-complete (the 47s do not
    contribute), PreGo, and trip 0 reads the clobbered work[1] as the
    next length (47), opens a sub-table with curr' = 45, and
    [it_enough] fires: it_loop 2 = Some (ItOverflow _).
    REPAIR CANDIDATE (g1+q6's call, not minted here as frozen): add the
    per-arm entry cap ALREADY PRESENT in build_accepts_of_kraft_STMT's
    own premise band ([forall len, In len l -> (len <= 15)%nat]; the
    CODES arm needs none — it is overflow-immune, proven below).

    TIER-A (fit-check-frozen interfaces): the assembly, the regime
    split, the regime-b arm, the main arm, the CODES arm (PROVEN).
    TIER-B (working machinery, explicitly amendable during the grind):
    the juncture abstraction, the chain accounting, the invariant, the
    step/guard/seed statements.  Per the commission terms, no Qed is
    spent on TIER-A/B bridge lemmas here; the only Qeds are the
    falsifier (decisive evidence), the CODES arm (g1-sanctioned
    trivial), and glue. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  The frozen text, verbatim (provenance: Gap7Strict.v ,
       lines 73 and 356-370).
   ========================================================================== *)

(* lens_of_list: RE-POINTED to Gap7Strict's export (g1-r4 landed ). *)

(** The PRE-REPAIR text (falsified below; kept as the documentary
    witness).  The LANDED Gap7Strict.EnoughFits_STMT carries the repair
    (the lens_capped premise) — re-pointed at g1-r4 (). *)
Definition EnoughFits_STMT_unrepaired : Prop :=
  forall ty (l : list nat) root0 c st,
    (ty = CT_CODES /\ (length l <= 19)%nat /\ root0 = 7
     \/ ty = CT_LENS /\ (length l <= 286)%nat /\ root0 = 9
     \/ ty = CT_DISTS /\ (length l <= 30)%nat /\ root0 = 6) ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    forall n t, it_loop n c st <> Some (ItOverflow t).

(* ==========================================================================
   1.  THE FALSIFIER (machine-checked).
   ========================================================================== *)

Definition bad_l : list nat := [1;2;2;47;47]%nat.

Lemma stmt_falsifier : ~ EnoughFits_STMT_unrepaired.
Proof.
  intro H.
  destruct (it_pre CT_LENS (lens_of_list bad_l) (Z.of_nat (length bad_l))
              9 tnone) as [| t0 | | c st] eqn:E;
    [ vm_compute in E; discriminate
    | vm_compute in E; discriminate
    | vm_compute in E; discriminate | ].
  assert (B : CT_LENS = CT_CODES /\ (length bad_l <= 19)%nat /\ 9 = 7
              \/ CT_LENS = CT_LENS /\ (length bad_l <= 286)%nat /\ 9 = 9
              \/ CT_LENS = CT_DISTS /\ (length bad_l <= 30)%nat /\ 9 = 6).
  { right; left. split; [reflexivity|]. split; [cbn; lia|reflexivity]. }
  specialize (H CT_LENS bad_l 9 c st B E 2%nat).
  vm_compute in E. injection E as Ec Est. subst c st.
  match goal with
  | H : forall t, ?loop <> Some (ItOverflow t) |- _ =>
      let r := eval vm_compute in loop in
      match r with
      | Some (ItOverflow ?tt) =>
          apply (H tt);
          vm_compute; reflexivity
      end
  end.
Qed.

(* ==========================================================================
   2.  THE CODES ARM (g1-sanctioned trivial; proven NOW, cap-free —
       CT_CODES is overflow-immune because it_enough has no CODES
       disjunct, Inftrees:106).
   ========================================================================== *)

Lemma it_enough_codes : forall u, it_enough CT_CODES u = false.
Proof. intro u. reflexivity. Qed.

Lemma it_pre_go_type : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st -> x_type c = ty.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H; cbv zeta in H.
  repeat (lazymatch type of H with
          | (if ?b then _ else _) = PreGo _ _ => destruct b
          | (match ?x with Some _ => _ | None => _ end) = PreGo _ _ =>
              destruct x
          end; try discriminate H).
  injection H as Hc _. subst c. reflexivity.
Qed.

Lemma it_step_codes_no_overflow : forall c st t,
  x_type c = CT_CODES -> it_step c st <> ItOverflow t.
Proof.
  intros c st t Hty. unfold it_step; cbv zeta.
  rewrite Hty, it_enough_codes.
  repeat lazymatch goal with
         | |- (if true then _ else _) <> _ => cbv iota
         | |- (if false then _ else _) <> _ => cbv iota
         | |- (if ?b then _ else _) <> _ => destruct b
         | |- _ => discriminate
         end.
Qed.

Lemma codes_no_overflow : forall n c st t,
  x_type c = CT_CODES -> it_loop n c st <> Some (ItOverflow t).
Proof.
  induction n as [|k IH]; intros c st t Hty; cbn [it_loop];
    [discriminate|].
  destruct (it_step c st) as [st'|st'|tv] eqn:ES.
  - apply IH; exact Hty.
  - discriminate.
  - intros _. exact (it_step_codes_no_overflow c st tv Hty ES).
Qed.

(** The CODES arm of the (repaired) target, in final form. *)
Lemma codes_arm : forall (l : list nat) root0 c st,
  it_pre CT_CODES (lens_of_list l) (Z.of_nat (length l)) root0 tnone
    = PreGo c st ->
  forall n t, it_loop n c st <> Some (ItOverflow t).
Proof.
  intros l root0 c st HP n t.
  exact (codes_no_overflow n c st t (it_pre_go_type _ _ _ _ _ _ _ HP)).
Qed.

(* ==========================================================================
   3.  TIER-A: the fit-check-frozen interfaces.
       [lens_capped] COPIES build_accepts_of_kraft_STMT's own cap
       vocabulary (Gap7Strict.v:379-...); [band2] is the frozen band's
       two live arms.  The REPAIRED target [EnoughFits_capped_STMT] is
       the assembly's conclusion — marked REPAIR-CANDIDATE, to be
       ratified (or respelled) by g1+q6.
   ========================================================================== *)

(* lens_capped: RE-POINTED to Gap7Strict's export. *)

Definition band2 (ty : Z) (l : list nat) (root0 : Z) : Prop :=
  ty = CT_LENS /\ (length l <= 286)%nat /\ root0 = 9
  \/ ty = CT_DISTS /\ (length l <= 30)%nat /\ root0 = 6.

(* EnoughFits_capped_STMT: RE-POINTED — the landed Gap7Strict.EnoughFits_STMT
   IS the capped text (c1 diff identical); all uses go to the tree name. *)

(** A1 — regime split.  PreGo at a live band arm forces the root to be
    either the band's nominal R0 (9/6) or the degenerate root = max.
    (Internally: completeness bounds min through the Kraft mass —
    286 < 2^9 gives min <= 8 for LENS, 30 < 2^5 gives min <= 4 for
    DISTS — and the max = 1 incomplete exception lands in root = max.) *)
Definition regime_split_STMT : Prop :=
  forall ty l root0 c st,
    band2 ty l root0 -> lens_capped l ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    x_root c = root0 \/ x_root c = x_max c.

(** A2 — the degenerate arm.  root = max means no sub-table can open
    (opening requires root < len1, and under the cap the work array is
    sort-intact so len1 <= max), hence no overflow.  NOTE: the cap is
    LOAD-BEARING here too — the falsifier's regime-(b) sibling
    ([1;2;2;47;47] itself, r = mx = 2) overflows without it. *)
Definition regime_b_STMT : Prop :=
  forall ty l root0 c st,
    lens_capped l ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    x_root c = x_max c ->
    forall n t, it_loop n c st <> Some (ItOverflow t).

(** A3 — the main arm: root = R0 at a live band arm.  THE theorem; its
    body is the TIER-B machinery (juncture abstraction + chain
    accounting + peak-dominance invariant + the DP oracle cells). *)
Definition main_arm_STMT : Prop :=
  forall ty l root0 c st,
    band2 ty l root0 -> lens_capped l ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    x_root c = root0 ->
    forall n t, it_loop n c st <> Some (ItOverflow t).

(** A4 — THE ASSEMBLY, proven from the three interfaces + the CODES arm.

    *)
Section Assembly.
  Hypothesis A1 : regime_split_STMT.
  Hypothesis A2 : regime_b_STMT.
  Hypothesis A3 : main_arm_STMT.

  Theorem enough_fits_capped : EnoughFits_STMT.
  Proof.
    intros ty l root0 c st BAND CAP HP n t.
    destruct BAND as [B0 | B2].
    - destruct B0 as (Hty & _ & _). subst ty.
      exact (codes_arm l root0 c st HP n t).
    - assert (B : band2 ty l root0) by exact B2.
      destruct (A1 ty l root0 c st B CAP HP) as [HR | HR].
      + exact (A3 ty l root0 c st B CAP HP HR n t).
      + exact (A2 ty l root0 c st CAP HP HR n t).
  Qed.
End Assembly.

(* ==========================================================================
   4.  TIER-B: the working machinery (AMENDABLE during the grind; the
       fit-check freezes TIER-A, and these sketches show a5 what the
       proof will look like and what it consumes).

       ABSTRACTION DECISION (DESIGN.md section 3 for the full
       rationale): the model's per-code trips SIMULATE the DP's inner
       use-loop iterations one-for-one; a juncture (length boundary)
       corresponds to one examineF node, and the model's within-length
       position k matches k iterations of the DP's use-loop accounting.
       enough.c's drain(least) equals `least` use-loop accounting steps
       (proved-by-inspection: both consume one slot per code, opening a
       fresh 2^(len-root) sub-table when the current one fills), so ONE
       uniform per-code accounting step [chain_code] serves the whole
       replay.  zlib's UPFRONT lookahead charge (it_subsz) vs the DP's
       INCREMENTAL doubling is reconciled by the DEBT term below.
   ========================================================================== *)

(** Remaining symbols at lengths [len..mx] (counts of CODES — never
    used-symbols; the bt_force2 trap is structurally avoided because
    everything reads the counts array). *)
Fixpoint rem_syms_aux (n : nat) (cnt : zarr) (l : Z) : Z :=
  match n with
  | O => 0
  | S k => cnt l + rem_syms_aux k cnt (l + 1)
  end.
Definition rem_syms (cnt : zarr) (len mx : Z) : Z :=
  rem_syms_aux (Z.to_nat (mx - len + 1)) cnt len.

(** Free bit patterns entering length [len]: twice the Kraft residual
    after lengths [1..len-1] ([F(len) = 2 * kraft_left(len-1)];
    F(1) = 2, F(len+1) = 2*(F(len) - cnt len) — the DP's own
    left-child law with use = cnt len). *)
Fixpoint kleft_aux (n : nat) (cnt : zarr) (l acc : Z) : Z :=
  match n with
  | O => acc
  | S k => kleft_aux k cnt (l + 1) (2 * acc - cnt l)
  end.
Definition kleft (cnt : zarr) (len : Z) : Z :=
  2 * kleft_aux (Z.to_nat (len - 1)) cnt 1 1.

(** One per-code accounting step of the DP's use loop
    (enough.c:433-442 tail; = one drain slot). *)
Definition chain_code (subsz mem rem : Z) : Z * Z :=
  if rem =? 0 then (mem + subsz, subsz - 1) else (mem, rem - 1).
Fixpoint chain_codes (k : nat) (subsz mem rem : Z) : Z * Z :=
  match k with
  | O => (mem, rem)
  | S k' => let '(m, r) := chain_code subsz mem rem in
            chain_codes k' subsz m r
  end.

(** Descending one length level (enough.c:435-436: the recursion's
    arguments): pay one doubling of the current sub-table if it is
    still open. *)
Definition chain_descend (subsz mem rem : Z) : Z * Z :=
  (mem + (if rem =? 0 then 0 else subsz), 2 * rem).

(** The DP-trace accounting at the boundary of length [len] for the
    ACTUAL code (its counts), seeded at (root+1) with (2^root, 0)
    exactly as enough_phase seeds examineF. *)
Fixpoint chain_at_aux (n : nat) (cnt : zarr) (rt l mem rem : Z) : Z * Z :=
  match n with
  | O => (mem, rem)
  | S k =>
      let subsz := 2 ^ (l - rt) in
      let '(m1, r1) := chain_codes (Z.to_nat (cnt l)) subsz mem rem in
      let '(m2, r2) := chain_descend subsz m1 r1 in
      chain_at_aux k cnt rt (l + 1) m2 r2
  end.
Definition chain_at (cnt : zarr) (rt len : Z) : Z * Z :=
  chain_at_aux (Z.to_nat (len - rt - 1)) cnt rt (rt + 1) (2 ^ rt) 0.

(** The per-juncture DP maximum: examineF from a fresh done-set.  The
    pruning set only skips REVISITED junctures inside one walk, so an
    empty seed gives the true max-over-completions from this node.
    Fuel: enough_phase's own [Z.to_nat mx + 1]. *)
Definition dp_peak (mx rt syms left len mem rem : Z) : Z :=
  fst (examineF (Z.to_nat mx + 1) mx rt syms left len mem rem
        (0, PM.empty unit)).

(** The upfront-vs-incremental DEBT: zlib charges a sub-table's FINAL
    size 2^curr at opening (it_subsz lookahead); the DP pays one
    doubling per descent.  At a state inside a sub-table (drop <> 0),
    the un-descended part of the upfront charge is
    [2^curr - 2^(len - drop)]. *)
Definition debt (st : ItSt) : Z :=
  if s_drop st =? 0 then 0
  else 2 ^ s_curr st - 2 ^ (s_len st - s_drop st).

(** B2 — the invariant (SKETCH; conjunct list amendable).  At a state
    [st] on the loop trajectory of a code with original counts [cnt0],
    root R0 and findmax [mx], with [k] codes already placed at the
    current length: *)
Definition InvB (ty R0 mx : Z) (cnt0 : zarr) (st : ItSt) : Prop :=
  let len := s_len st in
  let k := Z.to_nat (cnt0 len - s_count st len) in
  let '(memB, remB) := chain_at cnt0 R0 len in
  let '(mem, rem) := chain_codes k (2 ^ (len - R0)) memB remB in
  (* i1: the model's charged space is covered by the DP accounting plus
         the current sub-table's un-descended upfront charge *)
  s_used st <= mem + debt st
  (* i2: the whole future stays under the band constant *)
  /\ dp_peak mx R0 (rem_syms cnt0 len mx) (kleft cnt0 len) len mem rem
       <= (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS)
  (* i3: debt justification — the remaining counts force the DP to
         descend the current sub-table to depth curr+drop, paying i1's
         debt (candidate spelling: it_subsz stability; amendable) *)
  /\ ((s_drop st =? 0) = false ->
      s_curr st
        = it_subsz 16%nat (s_count st) (s_drop st) mx
            (s_len st - s_drop st) (Z.shiftl 1 (s_len st - s_drop st))).

(** B3 — step preservation (SKETCH): one it_step from an invariant
    state lands in an invariant state (ItCont), breaks (ItBreak), or is
    REFUTED as overflow by B4.  Stated at trip granularity; the length-
    boundary/within-length split lives in the proof. *)
Definition step_preserves_STMT : Prop :=
  forall ty R0 mx cnt0 c st st',
    (* ctx coherence premises elided in the sketch: x_root c = R0,
       x_max c = mx, s_count-vs-cnt0 prefix agreement, work-integrity
       under lens_capped — spelled at grind time *)
    InvB ty R0 mx cnt0 st ->
    it_step c st = ItCont st' ->
    InvB ty R0 mx cnt0 st'.

(** B4 — guard discharge (SKETCH): at an opening from an invariant
    state, the freshly charged used' passes the guard, i.e. it_step
    cannot return ItOverflow. *)
Definition guard_discharge_STMT : Prop :=
  forall ty R0 mx cnt0 c st t,
    InvB ty R0 mx cnt0 st ->
    it_step c st <> ItOverflow t.

(** B5 — the seed: the initial PreGo state satisfies InvB, via
    (B5a) countF-positivity: a juncture reached by an actual code has
          countF >= 1, hence memo_nonzero, hence enough_phase WALKS it;
    (B5b) the walked max is enough_bound's value;
    (B5c) the two native_compute cells (LANDED, imported from
          EnoughCheck: c_286_9_15 / c_30_6_15). *)
Definition seed_STMT : Prop :=
  forall ty l root0 c st,
    band2 ty l root0 -> lens_capped l ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    x_root c = root0 ->
    InvB ty root0 (x_max c)
      (it_count (Z.to_nat (Z.of_nat (length l))) 0 (lens_of_list l) zzero)
      st.

(** The oracle cells this design consumes, c_286_9_15 (enough_run 286 9
    15 = Some (_, Some 852)) and c_30_6_15 (enough_run 30 6 15 =
    Some (_, Some 592)), are exported by EnoughCheck.  This file no longer
    imports EnoughCheck: the range-split proof of c_286_9_15
    (EnoughSplit.v) is built on the memo-soundness files, which import
    this one. *)
