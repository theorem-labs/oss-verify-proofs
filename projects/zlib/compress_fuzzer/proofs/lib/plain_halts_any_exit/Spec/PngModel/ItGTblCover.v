(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblCover — the ROOT-REGION COVERAGE theorem for [inflate_table].

    GTBL-ARMS lane, 2026-08-18.  Own scratch, a working folder.
    Layer 4 of four: [ItGTblRev.v] (bit reversal + the increment law),
    [ItGTblGeom.v] (unit-crossing geometry + the Kraft mass),
    [ItGTblSortWin.v] (sorted-work placement, offsets, max/min), this file
    (the loop invariant and the theorem).

    THE OBLIGATION, lenext-repair's statement (LfxCoverStmt.v, md5 ),
    name adopted verbatim so there is one clause and two consumers:

<<
      TblBitsPosBelow (root : Z) (t : ztbl) : Prop :=
        forall i, 0 <= i < 2 ^ root -> c_bits (t i) <> 0
>>

    SPEC-SIDE ONLY: this chain never mentions [ItModel], so the consumer does
    not wait on the model-to-model bridge for this fact.

    WHY A POSITION AND NOT A WRITTEN SET.  Every write [inflate_table] performs
    stores a NONZERO bits field, so coverage is MONOTONE and a LOWER bound is
    all that is ever needed.  [CovBelow root t P] says "every root unit
    entirely below the position [P] holds a written entry"; the loop advances
    [P] by [2 ^ (15 - len)] per code and [huff] IS [P] in reversed form.

    THE TWO INPUTS, and neither is optional:
    - COMPLETENESS.  [it_kraft] pins [lft = 2^15 - mass cnt0]; at the exit all
      counts are zero, so [P] ends at [mass cnt0], which is the whole table
      exactly when [lft = 0].
    - SORTEDNESS.  Without it the theorem is FALSE, not merely unproven: an
      out-of-order trip in the sub-table phase can take a length below [root],
      which writes NOTHING into the root region ([incr] becomes 0 and the fill
      count is 0) while the position still advances past a whole unit.  The
      same fact is what makes [c_bits <> 0] free: a length-0 symbol would be
      written with [bits = len - drop = 0].  [ItGTblSortWin.v] supplies it. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblRev ItGTblGeom ItGTblSortWin.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(** ** 1.  The payload predicate, and why every write preserves it *)

Definition TblBitsPosBelow (root : Z) (t : ztbl) : Prop :=
  forall i, 0 <= i < 2 ^ root -> c_bits (t i) <> 0.

(** "Every root unit entirely below [P] holds a written entry."  Antitone in
    [P] (a smaller position claims less) and monotone under writes. *)
Definition CovBelow (root : Z) (t : ztbl) (P : Z) : Prop :=
  forall j, 0 <= j < 2 ^ root ->
    (zrev (Z.to_nat root) j + 1) * 2 ^ (15 - root) <= P ->
    1 <= c_bits (t j) <= root.

Lemma cov_le : forall root t P Q,
  CovBelow root t Q -> P <= Q -> CovBelow root t P.
Proof. intros root t P Q H Hpq j Hj Hu. apply H; [exact Hj | lia]. Qed.

Lemma cov_tset : forall root t P i e,
  CovBelow root t P -> 1 <= c_bits e <= root -> CovBelow root (tset t i e) P.
Proof.
  intros root t P i e H He j Hj Hu.
  destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite tset_same. exact He.
  - rewrite tset_other by exact Hne. apply H; assumption.
Qed.

Lemma cov_fill : forall root n t bi incr h P,
  CovBelow root t P -> 1 <= c_bits h <= root ->
  CovBelow root (it_fill n t bi incr h) P.
Proof.
  intros root n. induction n as [|k IH]; intros t bi incr h P H Hh; cbn [it_fill].
  - exact H.
  - apply IH; [| exact Hh]. apply cov_tset; assumption.
Qed.

(** [mkCodeT]'s bits field, at the only widths this file writes. *)
Lemma bits_mkCodeT : forall op b v, 0 <= b < 256 -> c_bits (mkCodeT op b v) = b.
Proof. intros op b v Hb. unfold mkCodeT. cbn [c_bits]. apply u8_id. exact Hb. Qed.

Lemma bits_here : forall c st,
  c_bits (it_here c st) = u8 (s_len st - s_drop st).
Proof.
  intros c st. unfold it_here.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c));
    [reflexivity|].
  destruct (Z.leb (x_match c) (x_work c (s_sym st))); reflexivity.
Qed.

Lemma bits_here_val : forall c st,
  0 <= s_len st - s_drop st < 256 ->
  c_bits (it_here c st) = s_len st - s_drop st.
Proof. intros c st H. rewrite bits_here. apply u8_id. lia. Qed.

(** ** 2.  Small [Z] bridges *)

Lemma shiftl1 : forall n, 0 <= n -> Z.shiftl 1 n = 2 ^ n.
Proof. intros n Hn. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma pow2_pos_z : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn. apply Z.pow_pos_nonneg; lia. Qed.

Lemma to_nat_pow : forall n, 0 <= n -> 2 ^ Z.of_nat (Z.to_nat n) = 2 ^ n.
Proof. intros n Hn. rewrite Z2Nat.id by lia. reflexivity. Qed.

(** ** 3.  The two coverage-extension lemmas — the whole geometry, wrapped

    SHORT CODES.  The trip's fill writes the residue class of [huff] modulo
    [2^len] inside [[0, 2^root)], and by [unit_cross_short] every unit the
    position newly completes lies in that class. *)

Lemma cov_step_short : forall root len huff t here,
  1 <= len <= root -> root <= 15 -> 0 <= huff < 2 ^ len ->
  1 <= c_bits here <= root ->
  CovBelow root t (zrev (Z.to_nat len) huff * 2 ^ (15 - len)) ->
  CovBelow root
    (it_fill (Z.to_nat (2 ^ root / 2 ^ len)) t huff (2 ^ len) here)
    (zrev (Z.to_nat len) huff * 2 ^ (15 - len) + 2 ^ (15 - len)).
Proof.
  intros root len huff t here Hlen Hroot Hhuff Hhere Hcov j Hj Hu.
  set (P := zrev (Z.to_nat len) huff * 2 ^ (15 - len)) in *.
  pose proof (pow2_pos_z len ltac:(lia)) as Hpl.
  pose proof (pow2_pos_z root ltac:(lia)) as Hpr.
  (* both association orders, so no step below depends on which one a Stdlib
     lemma happens to produce *)
  assert (Hpow : 2 ^ (root - len) * 2 ^ len = 2 ^ root).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hpow' : 2 ^ len * 2 ^ (root - len) = 2 ^ root) by (rewrite <- Hpow; ring).
  destruct (Z_le_gt_dec ((zrev (Z.to_nat root) j + 1) * 2 ^ (15 - root)) P) as [Hold|Hnew].
  - (* already covered before this trip: the fill only adds *)
    apply (cov_fill root _ t huff (2 ^ len) here P Hcov Hhere j Hj Hold).
  - (* newly completed: [j] is in the write class *)
    assert (Hmod : j mod 2 ^ len = huff).
    { pose proof (unit_cross_short (Z.to_nat root) (Z.to_nat len) huff j
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hx.
      rewrite !to_nat_pow in Hx by lia.
      rewrite !Z2Nat.id in Hx by lia.
      apply Hx; [ lia | lia | lia | lia ]. }
    assert (Hdiv : j = huff + (j / 2 ^ len) * 2 ^ len).
    { pose proof (Zdiv.Z_div_mod_eq_full j (2 ^ len)) as He.
      rewrite Hmod in He. lia. }
    assert (Hq : 0 <= j / 2 ^ len < 2 ^ (root - len)).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; [lia|]. rewrite Hpow'. lia. }
    (* explicit arguments: with [incr] left as an evar the side-condition
       tactic runs against [0 < ?incr] and fails with "Cannot find witness" *)
    rewrite (it_fill_get (Z.to_nat (2 ^ root / 2 ^ len)) t huff (2 ^ len) here j
                         ltac:(lia)).
    assert (Hn : Z.of_nat (Z.to_nat (2 ^ root / 2 ^ len)) = 2 ^ (root - len)).
    { rewrite Z2Nat.id.
      - rewrite <- Hpow, Z.div_mul by lia. reflexivity.
      - apply Z.div_pos; lia. }
    rewrite Hn.
    replace ((Z.leb huff j) && (Z.ltb j (huff + 2 ^ (root - len) * 2 ^ len))
             && (Z.eqb ((j - huff) mod 2 ^ len) 0)) with true.
    + exact Hhere.
    + symmetry.
      apply andb_true_intro. split.
      * apply andb_true_intro. split.
        -- apply Z.leb_le. lia.
        -- apply Z.ltb_lt. rewrite Hpow. lia.
      * apply Z.eqb_eq.
        replace (j - huff) with ((j / 2 ^ len) * 2 ^ len) by lia.
        apply Z.mod_mul. lia.
Qed.

(** LONG CODES.  The trip's fill lands entirely at or above [2^root], so the
    root region is untouched; by [unit_cross_long] the only unit the position
    can newly complete is the current code's own root prefix, which already
    carries its sub-table pointer. *)
Lemma cov_step_long : forall root len huff t n bi incr here,
  1 <= root -> root < len -> len <= 15 -> 0 <= huff < 2 ^ len ->
  2 ^ root <= bi -> 0 < incr ->
  CovBelow root t (zrev (Z.to_nat len) huff * 2 ^ (15 - len)) ->
  1 <= c_bits (t (huff mod 2 ^ root)) <= root ->
  CovBelow root (it_fill n t bi incr here)
    (zrev (Z.to_nat len) huff * 2 ^ (15 - len) + 2 ^ (15 - len)).
Proof.
  intros root len huff t n bi incr here Hr Hrl Hl Hhuff Hbi Hincr Hcov Hlow j Hj Hu.
  set (P := zrev (Z.to_nat len) huff * 2 ^ (15 - len)) in *.
  (* the fill misses the root region entirely *)
  assert (Hmiss : it_fill n t bi incr here j = t j).
  { rewrite (it_fill_get _ _ _ _ _ j Hincr).
    replace (Z.leb bi j) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity. }
  rewrite Hmiss.
  destruct (Z_le_gt_dec ((zrev (Z.to_nat root) j + 1) * 2 ^ (15 - root)) P) as [Hold|Hnew].
  - apply Hcov; assumption.
  - assert (Hj' : j = huff mod 2 ^ root).
    { pose proof (unit_cross_long (Z.to_nat root) (Z.to_nat len) huff j
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hx.
      rewrite !to_nat_pow in Hx by lia.
      rewrite !Z2Nat.id in Hx by lia.
      apply Hx; [ lia | lia | lia | lia ]. }
    rewrite Hj'. exact Hlow.
Qed.

(** ** 4.  The position advances by exactly one code's worth *)

Definition Pos (M0 : Z) (st : ItSt) : Z := M0 - it_mass 15%nat 1 (s_count st).

Lemma pos_advance : forall M0 cnt len,
  1 <= len <= 15 ->
  M0 - it_mass 15%nat 1 (zset cnt len (cnt len - 1))
  = (M0 - it_mass 15%nat 1 cnt) + 2 ^ (15 - len).
Proof.
  intros M0 cnt len Hlen.
  rewrite (it_mass_dec 15%nat 1 cnt len ltac:(cbn; lia)).
  replace (1 + Z.of_nat 15 - 1 - len) with (15 - len) by (cbn; lia).
  lia.
Qed.

(** ** 5.  The invariant

    Written out flat rather than with [let]s: a [let] in a statement hides the
    scrutinee from [destruct], which cost this chain a day once already. *)

Definition CovInv (c : ItCtx) (cnt0 : zarr) (st : ItSt) : Prop :=
  (* widths *)
  1 <= s_len st <= 15
  /\ 0 <= s_huff st < 2 ^ s_len st
  (* the sort window: which symbol the next trip processes *)
  /\ sw_offs cnt0 (s_len st) <= s_sym st
  /\ s_sym st < sw_offs cnt0 (s_len st) + cnt0 (s_len st)
  (* the counts, as a function of how far the sweep has got *)
  /\ (forall l, 1 <= l <= 15 ->
        s_count st l = (if Z.ltb l (s_len st) then 0
                        else if Z.eqb l (s_len st)
                             then sw_offs cnt0 (s_len st) + cnt0 (s_len st) - s_sym st
                             else cnt0 l))
  (* the position link: [huff] IS the position, in reversed form *)
  /\ Pos (it_mass 15%nat 1 cnt0) st
     = zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
  (* the payload *)
  /\ CovBelow (x_root c) (s_tbl st) (Pos (it_mass 15%nat 1 cnt0) st)
  (* the two phases, and they are exclusive *)
  /\ ( (s_drop st = 0 /\ s_curr st = x_root c /\ s_next st = 0
        /\ s_low st = 4294967295 /\ s_len st <= x_root c)
       \/ (s_drop st = x_root c /\ x_root c < s_len st
           /\ 2 ^ x_root c <= s_next st
           /\ s_low st = s_huff st mod 2 ^ x_root c
           /\ 1 <= c_bits (s_tbl st (s_low st)) <= x_root c) ).

(** What the caller's context has to be for the invariant to mean anything.
    Every clause is discharged from [it_pre] in §9. *)
Definition CovCtxOk (c : ItCtx) (cnt0 : zarr) : Prop :=
  1 <= x_root c <= 15
  /\ x_mask c = 2 ^ x_root c - 1
  /\ 1 <= x_max c <= 15
  /\ cnt0 (x_max c) <> 0
  /\ (forall l, x_max c < l <= 15 -> cnt0 l = 0)
  /\ (forall l, 1 <= l <= 15 -> 0 <= cnt0 l)
  /\ 0 <= x_codes c
  /\ (forall i, 0 <= i < x_codes c -> 0 <= x_lens c i <= 15)
  /\ cnt0 = sw_cnt (x_lens c) (x_codes c)
  /\ x_work c = sw_work (x_lens c) (x_codes c)
  (* the code is not over-subscribed: [it_kraft] returning [Some lft] with
     [lft >= 0] is exactly this, and §9 discharges it there *)
  /\ it_mass 15%nat 1 cnt0 <= 2 ^ 15
  (* ACCEPTED means one of exactly two things.  zlib rejects every incomplete
     code except a single one-bit one ([it_incomplete], Inftrees.v:174), so
     either the mass is the whole table or [max = 1] and it is half of it —
     and in the second case [it_finish] writes the entry the loop does not. *)
  /\ (it_mass 15%nat 1 cnt0 = 2 ^ 15
      \/ (x_max c = 1 /\ it_mass 15%nat 1 cnt0 = 2 ^ 14))
  (* [root] is clamped to [max] before the loop starts *)
  /\ x_root c <= x_max c.

(** ** 6.  The window toolkit

    Everything below is bookkeeping about where the sort put the symbols; the
    geometry is finished.  [sw_offs cnt] is a cumulative layout on [1..15]
    ONLY (fuel 14 from index 1), so every step lemma carries [<= 15] and the
    total is [sw_offs cnt 15 + cnt 15], never [sw_offs cnt 16]. *)

Lemma it_mass_zero_inv : forall n len cnt,
  (forall j, len <= j < len + Z.of_nat n -> 0 <= cnt j) ->
  it_mass n len cnt = 0 ->
  forall j, len <= j < len + Z.of_nat n -> cnt j = 0.
Proof.
  induction n as [|k IH]; intros len cnt Hnn Hm j Hj; [cbn in Hj; lia|].
  cbn [it_mass] in Hm.
  assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hrest : 0 <= it_mass k (len + 1) cnt).
  { apply it_mass_nonneg. intros i Hi. apply Hnn. rewrite Nat2Z.inj_succ. lia. }
  assert (H0 : 0 <= cnt len) by (apply Hnn; rewrite Nat2Z.inj_succ; lia).
  assert (Hcl : cnt len = 0) by nia.
  assert (Hz : it_mass k (len + 1) cnt = 0) by nia.
  destruct (Z.eq_dec j len) as [->|Hne]; [exact Hcl|].
  apply (IH (len + 1) cnt).
  - intros i Hi. apply Hnn. rewrite Nat2Z.inj_succ. lia.
  - exact Hz.
  - rewrite Nat2Z.inj_succ in Hj. lia.
Qed.

Lemma offs_top : forall cnt l,
  (forall i, 1 <= i <= 15 -> 0 <= cnt i) -> 1 <= l <= 15 ->
  sw_offs cnt l + cnt l <= sw_offs cnt 15 + cnt 15.
Proof.
  intros cnt l Hnn Hl.
  destruct (Z.eq_dec l 15) as [->|Hne]; [lia|].
  (* right to left: the goal carries [sw_offs cnt l + cnt l], not [sw_offs cnt (l+1)] *)
  rewrite <- (sw_offs_step cnt l ltac:(lia)).
  assert (sw_offs cnt (l + 1) <= sw_offs cnt 15)
    by (apply sw_offs_mono; [exact Hnn | lia | lia]).
  pose proof (Hnn 15 ltac:(lia)). lia.
Qed.

Lemma offs_nonneg : forall cnt l,
  (forall i, 1 <= i <= 15 -> 0 <= cnt i) -> 1 <= l <= 15 -> 0 <= sw_offs cnt l.
Proof.
  intros cnt l Hnn Hl.
  assert (sw_offs cnt 1 <= sw_offs cnt l)
    by (apply sw_offs_mono; [exact Hnn | lia | lia]).
  rewrite sw_offs_1 in *. lia.
Qed.

(** The length's window is exhausted and there IS a next symbol: the next
    length is strictly greater, its window starts exactly here, and every
    length skipped in between has no symbols at all. *)
Lemma cov_next_window : forall c cnt0 len sym,
  CovCtxOk c cnt0 ->
  1 <= len <= 15 ->
  sw_offs cnt0 len <= sym < sw_offs cnt0 len + cnt0 len ->
  sym + 1 = sw_offs cnt0 len + cnt0 len ->
  sym + 1 < sw_offs cnt0 15 + cnt0 15 ->
  exists l1, len < l1 <= 15
    /\ sw_offs cnt0 l1 = sym + 1
    /\ 0 < cnt0 l1
    /\ x_lens c (x_work c (sym + 1)) = l1
    /\ (forall l, len < l < l1 -> cnt0 l = 0).
Proof.
  intros c cnt0 len sym Hctx Hlen Hwin Hend Hnext.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof (offs_nonneg cnt0 len Hnn ltac:(lia)) as Hoff0.
  assert (Hlen14 : len <= 14).
  { destruct (Z.eq_dec len 15) as [->|Hne]; [|lia].
    pose proof (offs_top cnt0 15 Hnn ltac:(lia)). lia. }
  assert (Hstep : sw_offs cnt0 (len + 1) = sw_offs cnt0 len + cnt0 len)
    by (apply sw_offs_step; lia).
  assert (Hex : exists l, 1 <= l <= 15 /\ sw_offs cnt0 l <= sym + 1
                          < sw_offs cnt0 l + cnt0 l).
  { rewrite Hcnt0. apply sw_window_exists; [exact Hcodes | exact Hlens |].
    rewrite <- Hcnt0. lia. }
  destruct Hex as [l1 [Hl1 Hl1win]].
  assert (Hgt : len < l1).
  { destruct (Z_le_gt_dec l1 len) as [Hle|Hgt]; [|lia]. exfalso.
    destruct (Z.eq_dec l1 len) as [->|Hne]; [lia|].
    assert (Hm : sw_offs cnt0 (l1 + 1) <= sw_offs cnt0 len)
      by (apply sw_offs_mono; [exact Hnn | lia | lia]).
    rewrite (sw_offs_step cnt0 l1 ltac:(lia)) in Hm. lia. }
  assert (Hstart : sw_offs cnt0 l1 = sym + 1).
  { assert (sw_offs cnt0 (len + 1) <= sw_offs cnt0 l1)
      by (apply sw_offs_mono; [exact Hnn | lia | lia]).
    lia. }
  exists l1. split; [lia|]. split; [exact Hstart|]. split; [lia|].
  split.
  - rewrite Hwork. apply sw_places; [ exact Hcodes | exact Hlens | lia | ].
    rewrite <- Hcnt0. lia.
  - intros l Hl.
    assert (Ha : sw_offs cnt0 (len + 1) <= sw_offs cnt0 l)
      by (apply sw_offs_mono; [exact Hnn | lia | lia]).
    assert (Hb : sw_offs cnt0 (l + 1) <= sw_offs cnt0 l1)
      by (apply sw_offs_mono; [exact Hnn | lia | lia]).
    rewrite (sw_offs_step cnt0 l ltac:(lia)) in Hb.
    pose proof (Hnn l ltac:(lia)). lia.
Qed.

(** The window is exhausted and there is NO next symbol: every longer length
    is empty, so the loop's [max] is the length just finished — which is the
    model's own break condition. *)
Lemma cov_exhausted : forall c cnt0 len sym,
  CovCtxOk c cnt0 ->
  1 <= len <= 15 ->
  sw_offs cnt0 len <= sym < sw_offs cnt0 len + cnt0 len ->
  sw_offs cnt0 15 + cnt0 15 <= sym + 1 ->
  (forall l, len < l <= 15 -> cnt0 l = 0) /\ x_max c = len.
Proof.
  intros c cnt0 len sym Hctx Hlen Hwin Hge.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof (offs_top cnt0 len Hnn ltac:(lia)) as Htop.
  assert (Hzero : forall l, len < l <= 15 -> cnt0 l = 0).
  { intros l Hl.
    assert (Hle1 : sw_offs cnt0 (len + 1) <= sw_offs cnt0 l)
      by (apply sw_offs_mono; [exact Hnn | lia | lia]).
    rewrite (sw_offs_step cnt0 len ltac:(lia)) in Hle1.
    pose proof (offs_top cnt0 l Hnn ltac:(lia)).
    pose proof (Hnn l ltac:(lia)). lia. }
  split; [exact Hzero|].
  assert (Hcl : 0 < cnt0 len) by lia.
  destruct (Z_le_gt_dec (x_max c) len) as [Hle|Hgt].
  - destruct (Z.eq_dec (x_max c) len) as [->|Hne]; [reflexivity|].
    exfalso. rewrite (Hmxz len ltac:(lia)) in Hcl. lia.
  - exfalso. rewrite (Hzero (x_max c) ltac:(lia)) in Hmxnz. now apply Hmxnz.
Qed.

(** ** 7.  The trip's fill extends coverage by exactly one code's worth

    Branch-independent: whatever the trip then does about sub-tables, the fill
    itself has already carried the payload from [P] to [P + 2^(15-len)].  The
    two phases use the two geometry lemmas and nothing else. *)

Lemma cov_after_fill : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  CovBelow (x_root c)
    (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
             (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
             (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
    (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)).
Proof.
  intros c cnt0 st Hctx Hinv.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)].
  - (* PHASE 1: drop = 0, curr = root, next = 0 — the fill is the root region's *)
    rewrite Hd, Hc, Hnx, Z.shiftr_0_r, Z.sub_0_r, Z.add_0_l.
    rewrite (shiftl1 (s_len st) ltac:(lia)), (shiftl1 (x_root c) ltac:(lia)).
    rewrite Hpos.
    (* dispatch per goal, never positionally: the goal order after [try lia]
       is not the statement's premise order *)
    (* the entry's bits field is its EXACT value, so both bounds are one [lia]:
       the lower from [1 <= len], the upper from the phase-1 clause [len <= root]
       — which is what huffman-id's obligation (b) needs. *)
    assert (Hbv : c_bits (it_here c st) = s_len st - s_drop st).
    { apply bits_here_val. rewrite Hd. lia. }
    apply cov_step_short;
      try lia;
      try (rewrite Hbv, Hd; lia);
      try (rewrite <- Hpos; exact Hcov).
  - (* PHASE 2: drop = root, the fill lands at or above [2^root] *)
    assert (Hincr : Z.shiftl 1 (s_len st - s_drop st) = 2 ^ (s_len st - s_drop st))
      by (apply shiftl1; lia).
    assert (Hsr : 0 <= Z.shiftr (s_huff st) (s_drop st)).
    { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_pos; [lia|].
      apply pow2_pos_z. lia. }
    rewrite Hincr, Hpos.
    apply (cov_step_long (x_root c) (s_len st) (s_huff st) (s_tbl st) _
             (s_next st + Z.shiftr (s_huff st) (s_drop st))
             (2 ^ (s_len st - s_drop st)) (it_here c st));
      try lia;
      try (apply pow2_pos_z; lia);
      try (rewrite <- Hpos; exact Hcov);
      try (rewrite <- Hlow; exact Hlb).
Qed.

(** ** 8.  Two more small facts, then the step *)

Lemma fill_miss_below : forall n t bi incr h j,
  0 < incr -> j < bi -> it_fill n t bi incr h j = t j.
Proof.
  intros n t bi incr h j Hincr Hj.
  rewrite (it_fill_get n t bi incr h j Hincr).
  replace (Z.leb bi j) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(** Widening the width does not move the position: the extra bits of a code
    that has just been extended are zero, and reversal sends them to the top. *)
Lemma pos_link_widen : forall len len1 h,
  1 <= len <= len1 -> len1 <= 15 -> 0 <= h < 2 ^ len ->
  zrev (Z.to_nat len1) h * 2 ^ (15 - len1) = zrev (Z.to_nat len) h * 2 ^ (15 - len).
Proof.
  intros len len1 h Hle H15 Hh.
  assert (HD : Z.to_nat len1 = (Z.to_nat len + Z.to_nat (len1 - len))%nat) by lia.
  assert (Hh' : 0 <= h < 2 ^ Z.of_nat (Z.to_nat len))
    by (rewrite (to_nat_pow len ltac:(lia)); exact Hh).
  rewrite HD, (zrev_widen (Z.to_nat len) (Z.to_nat (len1 - len)) h Hh').
  rewrite (Z2Nat.id (len1 - len)) by lia.
  rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
  f_equal. f_equal. lia.
Qed.

(** The invariant's eight clauses, dispatched BY THE GOAL'S HEAD.  [lia] can
    prove the phase DISJUNCT outright in the leaves where the fields are
    unchanged, which then leaves nothing for the [right]/[left] that follows and
    the proof fails with a bullet error three lines later; the [fail 1] guard
    keeps the disjunct for the leaf-specific code.  (Fleet rule: guard tactics
    on the goal's head, and never dispatch positionally.) *)
(** ONE tactic per goal, chosen by the goal's HEAD — not a [first [...]] sweep.
    The sweep is quadratic here: cost is goals x candidate tactics x TERM SIZE,
    and these goals carry the whole [it_fill] expression, so a five-way [first]
    over eight goals in six leaves took minutes where the shape match takes
    seconds.  (Registered cost model: large terms => no search.) *)
Ltac cov_split Hc Hpl Hcf Hpb :=
  (* KIND-BASED, not [repeat split]: the payload clause's conclusion is now
     [1 <= c_bits _ <= root], itself a conjunction, so a bare [repeat split]
     reaches THROUGH the clause and leaves its two halves with [j] introduced —
     goals no alternative names.  Splitting only on an explicit [/\] head cannot. *)
  repeat match goal with |- _ /\ _ => split end;
    match goal with
    | |- _ \/ _ => idtac
    | |- forall _, _ => intros l Hl; apply Hc; lia
    | |- CovBelow _ _ _ =>
        first [ exact Hcf | apply cov_tset; [ exact Hcf | rewrite Hpb; lia ] ]
    | |- _ = _ => first [ apply Hpl; lia | lia ]
    | _ => lia
    end.

(** THE STEP.  Every fall-through trip preserves the invariant. *)
Lemma cov_step_cont : forall c cnt0 st st',
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> it_step c st = ItCont st' ->
  CovInv c cnt0 st'.
Proof.
  intros c cnt0 st st' Hctx Hinv Hstep.
  pose proof (cov_after_fill c cnt0 st Hctx Hinv) as Hfill.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv2.
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1)) in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  (* --- the counts after the trip --- *)
  assert (Hcnt1 : forall l, 1 <= l <= 15 ->
            cnt1 l = (if Z.ltb l (s_len st) then 0
                      else if Z.eqb l (s_len st)
                           then sw_offs cnt0 (s_len st) + cnt0 (s_len st) - (s_sym st + 1)
                           else cnt0 l)).
  { intros l Hl. unfold cnt1, zset.
    destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
    - rewrite (Hcnt (s_len st) ltac:(lia)), Z.ltb_irrefl, Z.eqb_refl. lia.
    - rewrite (Hcnt l Hl).
      destruct (Z.ltb l (s_len st)); [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)); [contradiction|reflexivity]. }
  assert (Hcnt1nn : forall l, 1 <= l <= 15 -> 0 <= cnt1 l).
  { intros l Hl. rewrite (Hcnt1 l Hl).
    destruct (Z.ltb l (s_len st)); [lia|].
    destruct (Z.eqb_spec l (s_len st)); [lia | apply Hnn; lia]. }
  (* --- the position advances by one code's worth --- *)
  assert (Hpos1 : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                  = Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)).
  { unfold cnt1. apply pos_advance. lia. }
  (* --- the reversed counter advanced (it cannot have wrapped and continued) --- *)
  assert (Hhuff' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite (to_nat_pow (s_len st) ltac:(lia)); exact Hhuff).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st) ltac:(lia) Hhuff') as Hinc.
  rewrite (Z2Nat.id (s_len st)) in Hinc by lia.
  assert (Hadv : 0 <= huff1 < 2 ^ s_len st
                 /\ zrev (Z.to_nat (s_len st)) huff1
                    = zrev (Z.to_nat (s_len st)) (s_huff st) + 1).
  { destruct Hinc as [[Hw Hz] | Hgood]; [exfalso | exact Hgood].
    (* the wrap: the position reaches 2^15, so every count is exhausted and the
       model must have taken ItBreak — which contradicts ItCont *)
    assert (Hp15 : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1 = 2 ^ 15).
    { rewrite Hpos1, Hpos, Hz.
      replace ((2 ^ s_len st - 1) * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
        with (2 ^ s_len st * 2 ^ (15 - s_len st)) by ring.
      rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hmzero : it_mass 15%nat 1 cnt1 = 0).
    { assert (0 <= it_mass 15%nat 1 cnt1)
        by (apply it_mass_nonneg; intros j Hj; apply Hcnt1nn; cbn in Hj; lia).
      lia. }
    assert (Hallz : forall l, 1 <= l <= 15 -> cnt1 l = 0).
    { intros l Hl. apply (it_mass_zero_inv 15%nat 1 cnt1);
        [ intros j Hj; apply Hcnt1nn; cbn in Hj; lia | exact Hmzero | cbn; lia ]. }
    assert (Hcl : 0 < cnt0 (s_len st)) by lia.
    assert (Hmxlen : x_max c = s_len st).
    { destruct (Z_le_gt_dec (x_max c) (s_len st)) as [Hle|Hgt].
      - destruct (Z.eq_dec (x_max c) (s_len st)) as [->|Hne]; [reflexivity|].
        exfalso. rewrite (Hmxz (s_len st) ltac:(lia)) in Hcl. lia.
      - exfalso.
        assert (cnt1 (x_max c) = cnt0 (x_max c)).
        { rewrite (Hcnt1 (x_max c) ltac:(lia)).
          destruct (Z.ltb_spec (x_max c) (s_len st)); [lia|].
          destruct (Z.eqb_spec (x_max c) (s_len st)); [lia|reflexivity]. }
        rewrite (Hallz (x_max c) ltac:(lia)) in *. now apply Hmxnz. }
    assert (Hhit : Z.eqb (cnt1 (s_len st)) 0 = true)
      by (apply Z.eqb_eq, Hallz; lia).
    rewrite Hhit, Hmxlen, Z.eqb_refl in Hstep. cbn [andb] in Hstep.
    discriminate Hstep. }
  destruct Hadv as [Hhuff1 Hzadv].
  (* --- coverage of the filled table, at the new position --- *)
  assert (Hcovfill : CovBelow (x_root c)
            (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                     (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                     (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
            (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1))
    by (rewrite Hpos1; exact Hfill).
  (* --- the new position link, for whatever the new length turns out to be --- *)
  assert (Hposlink : forall len1, s_len st <= len1 -> len1 <= 15 ->
            it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
            = zrev (Z.to_nat len1) huff1 * 2 ^ (15 - len1)).
  { intros len1 Hge H15.
    rewrite (pos_link_widen (s_len st) len1 huff1 ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite Hpos1, Hpos, Hzadv. ring. }
  (* --- the sub-table pointer's own bits field --- *)
  assert (Hptrbits : forall a b, c_bits (mkCodeT a (x_root c) b) = x_root c)
    by (intros a b; apply bits_mkCodeT; lia).
  (* --- low' is the root prefix of the new code --- *)
  assert (Hlowmod : Z.land huff1 (x_mask c) = huff1 mod 2 ^ x_root c).
  { rewrite Hmask. apply land_ones_mod. lia. }
  (* --- and it is never the phase-1 sentinel --- *)
  assert (Hnotsent : Z.land huff1 (x_mask c) <> 4294967295).
  { rewrite Hlowmod.
    assert (0 <= huff1 mod 2 ^ x_root c < 2 ^ x_root c)
      by (apply Z.mod_pos_bound, pow2_pos_z; lia).
    assert (2 ^ x_root c <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    cbn in *. lia. }
  assert (Hf0 : 0 <= Z.shiftl 1 (s_curr st))
    by (apply (proj2 (Z.shiftl_nonneg 1 (s_curr st))); lia).
  (* --- BOOKKEEPING for the two possible new lengths --- *)
  assert (Hbook_same : cnt1 (s_len st) <> 0 ->
            sw_offs cnt0 (s_len st) <= s_sym st + 1
            /\ s_sym st + 1 < sw_offs cnt0 (s_len st) + cnt0 (s_len st)).
  { intros Hh. rewrite (Hcnt1 (s_len st) ltac:(lia)) in Hh.
    rewrite Z.ltb_irrefl, Z.eqb_refl in Hh.
    pose proof (Hcnt1nn (s_len st) ltac:(lia)) as Hnn1.
    rewrite (Hcnt1 (s_len st) ltac:(lia)) in Hnn1.
    rewrite Z.ltb_irrefl, Z.eqb_refl in Hnn1. lia. }
  assert (Hbook_next : cnt1 (s_len st) = 0 -> s_len st <> x_max c ->
            exists l1, s_len st < l1 <= 15
              /\ sw_offs cnt0 l1 = s_sym st + 1
              /\ 0 < cnt0 l1
              /\ x_lens c (x_work c (s_sym st + 1)) = l1
              /\ (forall l, 1 <= l <= 15 ->
                    cnt1 l = (if Z.ltb l l1 then 0
                              else if Z.eqb l l1
                                   then sw_offs cnt0 l1 + cnt0 l1 - (s_sym st + 1)
                                   else cnt0 l))).
  { intros Hh Hne.
    rewrite (Hcnt1 (s_len st) ltac:(lia)), Z.ltb_irrefl, Z.eqb_refl in Hh.
    assert (Hend : s_sym st + 1 = sw_offs cnt0 (s_len st) + cnt0 (s_len st)) by lia.
    assert (Hlt : s_sym st + 1 < sw_offs cnt0 15 + cnt0 15).
    { destruct (Z_lt_le_dec (s_sym st + 1) (sw_offs cnt0 15 + cnt0 15)) as [H|H];
        [exact H | exfalso].
      destruct (cov_exhausted c cnt0 (s_len st) (s_sym st) Hctx2 ltac:(lia)
                  ltac:(lia) ltac:(lia)) as [_ Hmxl]. congruence. }
    destruct (cov_next_window c cnt0 (s_len st) (s_sym st) Hctx2 ltac:(lia)
                ltac:(lia) Hend Hlt) as [l1 (Hl1 & Hstart & Hpos1' & Hlensym & Hgap)].
    exists l1. split; [lia|]. split; [exact Hstart|]. split; [lia|].
    split; [exact Hlensym|].
    intros l Hl. rewrite (Hcnt1 l Hl).
    destruct (Z.ltb_spec l l1) as [Hll|Hll].
    - destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)) as [->|H2]; [lia|].
      rewrite (Hgap l ltac:(lia)). reflexivity.
    - destruct (Z.eqb_spec l l1) as [->|H2].
      + destruct (Z.ltb_spec l1 (s_len st)) as [H3|H3]; [lia|].
        destruct (Z.eqb_spec l1 (s_len st)) as [H4|H4]; [lia|]. lia.
      + destruct (Z.ltb_spec l (s_len st)) as [H3|H3]; [lia|].
        destruct (Z.eqb_spec l (s_len st)) as [H4|H4]; [lia|reflexivity]. }
  (* --- now the branches.  Dispatch per goal, never positionally: [repeat
         split; try lia] leaves the remaining goals in an order that is not the
         definition's clause order, and bullets keyed on that order silently
         apply the wrong tactic to the wrong goal. --- *)
  destruct (Z.eqb (cnt1 (s_len st)) 0) eqn:Hhit.
  - (* the current length is exhausted *)
    apply Z.eqb_eq in Hhit.
    destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq;
      cbn [andb] in Hstep; [discriminate Hstep|].
    apply Z.eqb_neq in Hmxeq.
    destruct (Hbook_next Hhit Hmxeq)
      as [l1 (Hl1 & Hstart & Hcl1 & Hlensym & Hcnt1')].
    rewrite Hlensym in Hstep.
    assert (Hh1l1 : 0 <= huff1 < 2 ^ l1).
    { assert (2 ^ s_len st <= 2 ^ l1) by (apply Z.pow_le_mono_r; lia). lia. }
    destruct (Z.ltb (x_root c) l1) eqn:Hgt.
    + apply Z.ltb_lt in Hgt.
      destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame;
        cbn [andb negb] in Hstep.
      * (* same root prefix: no new sub-table, so we are in the sub-table phase *)
        apply Z.eqb_eq in Hsame.
        destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; rewrite Hlow in Hsame; contradiction|].
        assert (Hlowkeep : 1 <= c_bits
                  (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                     (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                     (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st) (s_low st))
                  <= x_root c).
        { rewrite fill_miss_below; [ exact Hlb | | ].
          - rewrite (shiftl1 (s_len st - s_drop st) ltac:(lia)). apply pow2_pos_z; lia.
          - assert (0 <= s_huff st mod 2 ^ x_root c < 2 ^ x_root c)
              by (apply Z.mod_pos_bound, pow2_pos_z; lia).
            assert (0 <= Z.shiftr (s_huff st) (s_drop st))
              by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos;
                  [lia | apply pow2_pos_z; lia]).
            lia. }
        injection Hstep as Hst'. subst st'.
        unfold CovInv, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl].
        cov_split Hcnt1' Hposlink Hcovfill Hptrbits.
        right. repeat split; try lia;
          try exact Hlowkeep;
          try (rewrite <- Hsame; exact Hlowmod).
      * (* new root prefix: a sub-table is created *)
        (* ABSTRACT [it_subsz] FIRST, then the branch.  [it_subsz]'s [left]
           argument doubles per level, so ANY tactic that whnf-reduces a term
           containing [it_subsz 16 ...] (injection, discriminate, cbn, lia's
           preprocessing) blows up exponentially: >10 min of CPU with no error
           and no output.  Nothing in the invariant mentions [s_curr] or
           [s_used] in this phase, so naming the sub-table width as an opaque
           variable costs nothing and keeps every later term small.  (Registered
           rule: parameterize the value and take the equality.) *)
        match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as curr' eqn:Hcurr'
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ => remember b as en eqn:Hen; destruct en
        end; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        unfold CovInv, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl].
        cov_split Hcnt1' Hposlink Hcovfill Hptrbits.
        right.
        destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)].
        -- rewrite Hd, Hc, Hnx, Z.eqb_refl.
           repeat split; try lia;
             try (rewrite (shiftl1 (x_root c) ltac:(lia)); lia);
             try exact Hlowmod;
             try (rewrite tset_same, Hptrbits; lia).
        -- rewrite Hd.
           replace (Z.eqb (x_root c) 0) with false
             by (symmetry; apply Z.eqb_neq; lia).
           repeat split; try lia;
             try exact Hlowmod;
             try (rewrite tset_same, Hptrbits; lia).
    + (* the new length still fits the root table *)
      apply Z.ltb_ge in Hgt.
      cbn [andb] in Hstep.
      injection Hstep as Hst'. subst st'.
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
        [| exfalso; lia].
      unfold CovInv, Pos.
      cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl].
      cov_split Hcnt1' Hposlink Hcovfill Hptrbits.
      left. repeat split; try lia.
  - (* the current length continues *)
    apply Z.eqb_neq in Hhit.
    cbn [andb] in Hstep.
    destruct (Hbook_same Hhit) as [HwL HwU].
    destruct (Z.ltb (x_root c) (s_len st)) eqn:Hgt.
    + apply Z.ltb_lt in Hgt.
      destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame;
        cbn [andb negb] in Hstep.
      * apply Z.eqb_eq in Hsame.
        destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; lia|].
        assert (Hlowkeep : 1 <= c_bits
                  (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                     (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                     (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st) (s_low st))
                  <= x_root c).
        { rewrite fill_miss_below; [ exact Hlb | | ].
          - rewrite (shiftl1 (s_len st - s_drop st) ltac:(lia)). apply pow2_pos_z; lia.
          - assert (0 <= s_huff st mod 2 ^ x_root c < 2 ^ x_root c)
              by (apply Z.mod_pos_bound, pow2_pos_z; lia).
            assert (0 <= Z.shiftr (s_huff st) (s_drop st))
              by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos;
                  [lia | apply pow2_pos_z; lia]).
            lia. }
        injection Hstep as Hst'. subst st'.
        unfold CovInv, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl].
        cov_split Hcnt1 Hposlink Hcovfill Hptrbits.
        right. repeat split; try lia;
          try exact Hlowkeep;
          try (rewrite <- Hsame; exact Hlowmod).
      * (* same treatment as the other sub-table leaf: abstract [it_subsz]
           before anything can try to reduce it *)
        match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as curr' eqn:Hcurr'
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ => remember b as en eqn:Hen; destruct en
        end; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; lia|].
        unfold CovInv, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl].
        cov_split Hcnt1 Hposlink Hcovfill Hptrbits.
        right. rewrite Hd.
        replace (Z.eqb (x_root c) 0) with false
          by (symmetry; apply Z.eqb_neq; lia).
        repeat split; try lia;
          try exact Hlowmod;
          try (rewrite tset_same, Hptrbits; lia).
    + apply Z.ltb_ge in Hgt.
      cbn [andb] in Hstep.
      injection Hstep as Hst'. subst st'.
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
        [| exfalso; lia].
      unfold CovInv, Pos.
      cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl].
      cov_split Hcnt1 Hposlink Hcovfill Hptrbits.
      left. repeat split; try lia.
Qed.

(** ** 8b.  The exit

    At the break every count is zero, so the position has reached the whole
    Kraft mass of the histogram.  For a COMPLETE code that is [2^15] and the
    root table is covered outright.  For the one incomplete code zlib accepts
    (a single one-bit code: [max = 1], hence [root = 1]) the position reaches
    only half the table, and the remaining entry is the one [it_finish]
    writes — so the fix-up is load-bearing, not decoration. *)

Lemma cov_step_break : forall c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> it_step c st = ItBreak st1 ->
  forall j, 0 <= j < 2 ^ x_root c -> 1 <= c_bits (it_finish st1 j) <= x_root c.
Proof.
  intros c cnt0 st st1 Hctx Hinv Hstep j Hj.
  pose proof (cov_after_fill c cnt0 st Hctx Hinv) as Hfill.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv2.
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1)) in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  (* [ItBreak] comes ONLY from the first branch, but seeing that on the other
     side needs the remaining [if]s split open first: with [hit0] false the
     hypothesis is still a nest of [if]s, all of whose leaves are [ItCont] or
     [ItOverflow], so a bare [discriminate] reports "not a discriminable
     equality" rather than closing the case. *)
  destruct (Z.eqb (cnt1 (s_len st)) 0) eqn:Hhit; cbn [andb] in Hstep;
    [| exfalso;
       repeat match type of Hstep with
              | (if ?b then _ else _) = _ => destruct b
              end;
       discriminate Hstep ].
  destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq; cbn [andb] in Hstep;
    [| exfalso;
       repeat match type of Hstep with
              | (if ?b then _ else _) = _ => destruct b
              end;
       discriminate Hstep ].
  apply Z.eqb_eq in Hhit. apply Z.eqb_eq in Hmxeq.
  (* the counts, and hence the mass, are exhausted *)
  assert (Hcnt1 : forall l, 1 <= l <= 15 -> cnt1 l = 0).
  { intros l Hl. unfold cnt1, zset.
    destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
    - unfold cnt1, zset in Hhit. rewrite Z.eqb_refl in Hhit. exact Hhit.
    - rewrite (Hcnt l Hl).
      destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)) as [H2|H2]; [contradiction|].
      apply Hmxz. lia. }
  assert (Hmass0 : it_mass 15%nat 1 cnt1 = 0)
    by (apply it_mass_zero_on; intros i Hi; apply Hcnt1; cbn in Hi; lia).
  assert (Hposbrk : Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
                    = it_mass 15%nat 1 cnt0).
  { unfold Pos in *. rewrite <- (pos_advance (it_mass 15%nat 1 cnt0)
                                  (s_count st) (s_len st) ltac:(lia)).
    unfold cnt1 in Hmass0. rewrite Hmass0. ring. }
  rewrite Hposbrk in Hfill.
  (* the fix-up write only ever adds *)
  injection Hstep as Hst1. subst st1.
  assert (Hbitsfix : forall a b v, 0 <= a - b < 256 ->
            c_bits (mkCodeT v (a - b) 0) = a - b)
    by (intros a b v Hab; rewrite bits_mkCodeT by lia; reflexivity).
  (* the reversed counter cannot have wrapped here unless the code is complete *)
  assert (Hhuff' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite (to_nat_pow (s_len st) ltac:(lia)); exact Hhuff).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st) ltac:(lia) Hhuff') as Hinc.
  rewrite (Z2Nat.id (s_len st)) in Hinc by lia.
  (* [unfold], not [cbn [it_finish]]: [cbn] declines to unfold a definition
     whose body is a match stuck on a symbolic scrutinee, and then silently
     leaves [it_finish {|...|}] in place. *)
  unfold it_finish.
  cbn [s_huff s_next s_len s_drop s_tbl].
  assert (Hh1nn : 0 <= huff1) by (destruct Hinc as [[Hw _] | [Hr _]]; lia).
  destruct Hcase as [Hfull | [Hmx1 Hhalf]].
  - (* COMPLETE: the position reached the whole table *)
    assert (Hcovj : 1 <= c_bits
              (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                 (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                 (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st) j) <= x_root c).
    { apply Hfill; [exact Hj|].
      rewrite Hfull.
      pose proof (zrev_lt (Z.to_nat (x_root c)) j) as Hlt.
      rewrite (to_nat_pow (x_root c) ltac:(lia)) in Hlt.
      pose proof (pow2_pos_z (15 - x_root c) ltac:(lia)).
      assert (Hsplit : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      nia. }
    destruct (Z.eqb huff1 0) eqn:Hz; [exact Hcovj|].
    destruct (Z.eq_dec j (s_next st + huff1)) as [->|Hne].
    + (* THE FIX-UP INDEX, and the upper bound makes this case split necessary
         where the lower bound did not: in the SUB-TABLE phase [len - drop] can
         EXCEED [root] (e.g. root 1, len 5), so `bits <= root` is FALSE of that
         entry — but its index is [s_next + huff1 >= 2^root], i.e. OUTSIDE the
         root region, so the case is vacuous exactly there.  The bound this file
         exports is about the ROOT REGION; sub-table entries carry wider bits. *)
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)].
      * rewrite tset_same, Hbitsfix; lia.
      * exfalso. lia.
    + rewrite tset_other by exact Hne. exact Hcovj.
  - (* INCOMPLETE-BUT-ACCEPTED: max = 1 forces root = 1, and the loop covers
       only the first of the two entries; [it_finish] writes the other *)
    assert (Hr1 : x_root c = 1) by lia.
    assert (Hl1 : s_len st = 1) by lia.
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)]; [|exfalso; lia].
    assert (Hzj : zrev (Z.to_nat (x_root c)) j = 0 \/ j = 1).
    { rewrite Hr1 in *. change (Z.to_nat 1) with 1%nat.
      destruct (Z.eq_dec j 1) as [->|Hne]; [right; reflexivity|].
      left. assert (j = 0) by (cbn in Hj; lia). subst j.
      apply zrev_zero. }
    destruct Hzj as [Hz0 | ->].
    + (* the covered half *)
      assert (Hcovj : 1 <= c_bits
                (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                   (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                   (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st) j) <= x_root c).
      { apply Hfill; [exact Hj|]. rewrite Hz0, Hhalf, Hr1. cbn. lia. }
      destruct (Z.eqb huff1 0) eqn:Hz; [exact Hcovj|].
      destruct (Z.eq_dec j (s_next st + huff1)) as [->|Hne].
      * rewrite tset_same, Hbitsfix; lia.
      * rewrite tset_other by exact Hne. exact Hcovj.
    + (* the entry the fix-up writes: [huff] wrapped to 1, at index 1 *)
      (* [lia] cannot evaluate [Z.pow]: [2 ^ (15 - 1)] and [2 ^ 14] are two
         different atoms to it, and the failure reads "Cannot find witness"
         as if a bound were missing.  Make the exponents syntactically equal. *)
      assert (Hposzero : Pos (it_mass 15%nat 1 cnt0) st = 0).
      { rewrite Hl1 in Hposbrk.
        replace (15 - 1) with 14 in Hposbrk by lia. lia. }
      assert (Hzh : zrev (Z.to_nat (s_len st)) (s_huff st) = 0).
      { rewrite Hpos in Hposzero.
        pose proof (pow2_pos_z (15 - s_len st) ltac:(lia)).
        pose proof (zrev_nonneg (Z.to_nat (s_len st)) (s_huff st)). nia. }
      assert (Hadv : zrev (Z.to_nat (s_len st)) huff1
                     = zrev (Z.to_nat (s_len st)) (s_huff st) + 1
                     /\ 0 <= huff1 < 2 ^ s_len st).
      { destruct Hinc as [[Hw Hz1] | [Hr Ha]]; [exfalso | tauto].
        (* do NOT [cbn in Hz1]: it rewrites the [zrev] application into a
           different atom and [lia] then sees no contradiction with [Hzh]
           at all ("Cannot find witness").  Rewrite [Hzh] INTO it instead. *)
        rewrite Hzh in Hz1. rewrite Hl1 in Hz1.
        change (2 ^ 1) with 2 in Hz1. lia. }
      destruct Hadv as [Hadv Hrange].
      assert (Hhuff1 : huff1 = 1).
      { apply (zrev_inj (Z.to_nat (s_len st))).
        - rewrite (to_nat_pow (s_len st) ltac:(lia)). lia.
        - rewrite (to_nat_pow (s_len st) ltac:(lia)), Hl1.
          change (2 ^ 1) with 2. lia.
        - rewrite Hadv, Hzh, Hl1. change (Z.to_nat 1) with 1%nat.
          rewrite (zrev_one 0). reflexivity. }
      (* [replace] would leave [if false then _ else _] unreduced and the
         [tset] rewrite would then find no subterm; [destruct] reduces it. *)
      destruct (Z.eqb huff1 0) eqn:Hz; [exfalso; apply Z.eqb_eq in Hz; lia|].
      replace (s_next st + huff1) with 1 by lia.
      rewrite tset_same, Hbitsfix; lia.
Qed.

(** The loop: every fall-through preserves the invariant, and the break lands
    on the exit lemma. *)
Lemma cov_loop : forall n c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  it_loop n c st = Some (ItBreak st1) ->
  forall j, 0 <= j < 2 ^ x_root c -> 1 <= c_bits (it_finish st1 j) <= x_root c.
Proof.
  induction n as [|k IH]; intros c cnt0 st st1 Hctx Hinv Hloop j Hj;
    cbn [it_loop] in Hloop; [discriminate Hloop|].
  destruct (it_step c st) as [st'|st'|t] eqn:Hs.
  - apply (IH c cnt0 st' st1 Hctx
            (cov_step_cont c cnt0 st st' Hctx Hinv Hs) Hloop j Hj).
  - (* which of the two names survives [injection ... as <-] is not ours to
       predict; let unification take the state from [Hs] *)
    injection Hloop as <-.
    apply (cov_step_break c cnt0 st _ Hctx Hinv Hs j Hj).
  - discriminate Hloop.
Qed.

(** ** 9.  From the loop to the model

    Three small scan facts the sort-window file does not carry (it was asked
    for the zero-below half only), then the prologue and the theorem. *)

Lemma findmin_ge : forall n m mx cnt, m <= mx -> m <= it_findmin n m mx cnt.
Proof.
  induction n as [|k IH]; intros m mx cnt Hm; cbn [it_findmin]; [lia|].
  destruct (Z.geb m mx) eqn:Hge; [lia|].
  (* [Z.geb_leb] is an equation between booleans, so it is a REWRITE, not an
     [apply]: chaining it as [apply Z.geb_leb, Z.leb_gt in Hge] fails. *)
  rewrite Z.geb_leb in Hge. apply Z.leb_gt in Hge.
  destruct (Z.eqb (cnt m) 0); [|lia].
  pose proof (IH (m + 1) mx cnt ltac:(lia)). lia.
Qed.

Lemma findmin_nz : forall n m mx cnt,
  it_findmin n m mx cnt <> mx -> cnt (it_findmin n m mx cnt) <> 0.
Proof.
  induction n as [|k IH]; intros m mx cnt Hne; cbn [it_findmin] in *; [lia|].
  destruct (Z.geb m mx) eqn:Hge; [lia|].
  destruct (Z.eqb (cnt m) 0) eqn:Hz.
  - apply (IH (m + 1) mx cnt Hne).
  - apply Z.eqb_neq. exact Hz.
Qed.

(** The first window starts at 0: every length below the minimum is empty, so
    the cumulative layout has not moved yet. *)
Lemma offs_zero_prefix : forall cnt m,
  1 <= m <= 15 -> (forall l, 1 <= l < m -> cnt l = 0) -> sw_offs cnt m = 0.
Proof.
  intros cnt m Hm Hz.
  remember (Z.to_nat (m - 1)) as d eqn:Hd. revert m Hm Hz Hd.
  induction d as [|d IH]; intros m Hm Hz Hd.
  - replace m with 1 by lia. apply sw_offs_1.
  - assert (Hm1 : 1 <= m - 1 <= 15) by lia.
    assert (Hprev : sw_offs cnt (m - 1) = 0)
      by (apply IH; [lia | intros l Hl; apply Hz; lia | lia]).
    rewrite (sw_offs_step' cnt (m - 1) m ltac:(lia) ltac:(lia)), Hprev.
    rewrite (Hz (m - 1) ltac:(lia)). lia.
Qed.

(** [it_mass] of a histogram whose only nonzero bucket is 1. *)
Lemma mass_only_one : forall cnt,
  (forall l, 1 < l <= 15 -> cnt l = 0) ->
  it_mass 15%nat 1 cnt = cnt 1 * 2 ^ 14.
Proof.
  (* [cbn [it_mass]] fully expands the fixpoint (the fuel is a literal) and
     then there is no [it_mass 14 2 cnt] subterm left to rewrite.  Peel exactly
     one level with [change] instead. *)
  intros cnt Hz.
  change (it_mass 15%nat 1 cnt)
    with (cnt 1 * 2 ^ Z.of_nat 14 + it_mass 14%nat (1 + 1) cnt).
  rewrite (it_mass_zero_on 14%nat (1 + 1) cnt);
    [ change (Z.of_nat 14) with 14; ring
    | intros j Hj; apply Hz; cbn in Hj; lia ].
Qed.

(** THE PROLOGUE.  Everything the loop layer assumes, discharged from
    [it_pre]'s own computation. *)
Lemma cov_pre : forall ty lens codes root0 t0 c st,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_pre ty lens codes root0 t0 = PreGo c st ->
  CovCtxOk c (sw_cnt lens codes) /\ CovInv c (sw_cnt lens codes) st.
Proof.
  intros ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre.
  unfold it_pre in Hpre. cbv zeta in Hpre.
  (* ---- peel [it_pre] first, so every later fact is about a NAME ---- *)
  set (cnt0 := it_count (Z.to_nat codes) 0 lens zzero) in *.
  assert (Hcnt0 : cnt0 = sw_cnt lens codes) by reflexivity.
  assert (Hworkeq : snd (it_sort (Z.to_nat codes) 0 lens
                           (it_offs 14%nat 1 cnt0 (zset zzero 1 0)) zzero)
                    = sw_work lens codes) by reflexivity.
  set (mx := it_findmax 15%nat MAXBITS cnt0) in *.
  destruct (Z.eqb mx 0) eqn:Hmx0; [discriminate Hpre|].
  apply Z.eqb_neq in Hmx0.
  set (mn := it_findmin 16%nat 1 mx cnt0) in *.
  set (r1 := if Z.ltb mx root0 then mx else root0) in *.
  set (r := if Z.ltb r1 mn then mn else r1) in *.
  destruct (it_kraft 15%nat 1 1 cnt0) as [lft|] eqn:Hk; [|discriminate Hpre].
  destruct (it_incomplete ty lft mx) eqn:Hinc; [discriminate Hpre|].
  match type of Hpre with
  | (if ?b then _ else _) = _ => remember b as en eqn:Hen; destruct en
  end; [discriminate Hpre|].
  injection Hpre as Hc Hst.
  (* ---- the max scan.  [change] folds the raw term onto [mx]; [clearbody]
     then makes it OPAQUE, and that is not cosmetic: [lia]'s preprocessing
     unfolds a let-bound variable and expands [it_findmax]'s 15 levels, after
     which even [mx <= 17] does not follow from [1 <= mx <= 15] — it fails
     with "Cannot find witness", which reads as a missing bound. ---- *)
  destruct (sw_findmax_15 cnt0) as [Hmxz Hmxcase].
  change (it_findmax 15%nat MAXBITS cnt0) with mx in Hmxz, Hmxcase.
  unfold MAXBITS in Hmxz, Hmxcase.
  assert (Hmxr : 1 <= mx <= 15) by (destruct Hmxcase as [H|H]; lia).
  assert (Hcntmx : cnt0 mx <> 0) by (destruct Hmxcase as [H|H]; [lia|tauto]).
  clearbody mx.
  (* ---- the min scan, same treatment ---- *)
  assert (Hmx17 : mx <= 17) by lia.
  destruct (sw_findmin_16 mx cnt0 Hmx17) as [Hmnz Hmnle].
  change (it_findmin 16%nat 1 mx cnt0) with mn in Hmnz, Hmnle.
  assert (Hmn1 : 1 <= mn) by (unfold mn; apply findmin_ge; lia).
  assert (Hcntmn : cnt0 mn <> 0).
  { destruct (Z.eq_dec mn mx) as [Heq|Hne]; [rewrite Heq; exact Hcntmx|].
    unfold mn. apply findmin_nz. exact Hne. }
  assert (Hmnmx : mn <= mx) by lia.
  clearbody mn.
  (* ---- the two clampings ---- *)
  assert (Hr1 : 1 <= r1 <= mx) by (unfold r1; destruct (Z.ltb_spec mx root0); lia).
  assert (Hr : mn <= r /\ r <= mx /\ 1 <= r <= 15)
    by (unfold r; destruct (Z.ltb_spec r1 mn); lia).
  clearbody r1. clearbody r.
  (* ---- the histogram is non-negative ---- *)
  assert (Hnn : forall l, 1 <= l <= 15 -> 0 <= cnt0 l)
    by (intros l Hl; rewrite Hcnt0; apply sw_cnt_nonneg).
  (* ---- the Kraft mass, and the two shapes an ACCEPTED code can have ---- *)
  assert (Hpow15 : 2 ^ 15 = 2 * 2 ^ 14)
    by (change (2 ^ 15) with 32768; change (2 ^ 14) with 16384; lia).
  assert (Hmass : lft = 2 ^ 15 - it_mass 15%nat 1 cnt0).
  { pose proof (it_kraft_mass 15%nat 1 1 cnt0 lft Hk) as H.
    change (Z.of_nat 15) with 15 in H. lia. }
  assert (Hlft0 : 0 <= lft)
    by (apply (it_kraft_nonneg 15%nat 1 1 cnt0); [lia|exact Hk]).
  assert (Hupper : it_mass 15%nat 1 cnt0 <= 2 ^ 15) by lia.
  assert (Hcase : it_mass 15%nat 1 cnt0 = 2 ^ 15
                  \/ (mx = 1 /\ it_mass 15%nat 1 cnt0 = 2 ^ 14)).
  { unfold it_incomplete in Hinc.
    apply andb_false_iff in Hinc as [Hlt|Hor].
    - left. apply Z.ltb_ge in Hlt. lia.
    - apply orb_false_iff in Hor as [_ Hne1].
      apply negb_false_iff, Z.eqb_eq in Hne1.
      assert (Hone : forall l, 1 < l <= 15 -> cnt0 l = 0)
        by (intros l Hl; apply Hmxz; lia).
      rewrite (mass_only_one cnt0 Hone) in *.
      assert (Hc1 : cnt0 1 <> 0) by (rewrite <- Hne1; exact Hcntmx).
      assert (Hc1nn : 0 <= cnt0 1) by (apply Hnn; lia).
      pose proof (pow2_pos_z 14 ltac:(lia)).
      assert (Hc1le : cnt0 1 <= 2) by nia.
      destruct (Z.eq_dec (cnt0 1) 2) as [He2|H2]; [left; rewrite He2; lia|].
      right. split; [lia|]. assert (Hc11 : cnt0 1 = 1) by lia.
      rewrite Hc11. ring. }
  (* ---- the two records ---- *)
  subst c st. split.
  (* Clause by clause, in the DEFINITION's order, with no search: a [try lia]
     sweep closes an unpredictable subset first (and [lia] will even intro a
     [forall] and split the [<= <=] notation, leaving two goals nobody named),
     after which any positional step lands on the wrong goal. *)
  - unfold CovCtxOk. cbn [x_root x_mask x_max x_codes x_lens x_work x_type].
    rewrite <- Hcnt0.
    split; [lia|].                                    (* 1 <= root <= 15 *)
    split; [rewrite (shiftl1 r ltac:(lia)); ring|].   (* mask = 2^root - 1 *)
    split; [lia|].                                    (* 1 <= max <= 15 *)
    split; [exact Hcntmx|].                           (* count[max] <> 0 *)
    split; [exact Hmxz|].                             (* zero above max *)
    split; [exact Hnn|].                              (* counts non-negative *)
    split; [lia|].                                    (* 0 <= codes *)
    split; [exact Hlens|].                            (* lens in range *)
    split; [reflexivity|].                            (* cnt0 is the histogram *)
    split; [exact Hworkeq|].                          (* work is the sorted array *)
    split; [exact Hupper|].                           (* not over-subscribed *)
    split; [exact Hcase|].                            (* complete, or max = 1 *)
    lia.                                              (* root <= max *)
  - unfold CovInv, Pos.
    cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl
         x_root x_mask x_max x_codes x_lens x_work].
    assert (Hoffmn : sw_offs cnt0 mn = 0)
      by (apply offs_zero_prefix; [lia | intros l Hl; apply Hmnz; lia]).
    pose proof (pow2_pos_z mn ltac:(lia)) as Hpmn.
    pose proof (Hnn mn ltac:(lia)) as Hnnmn.
    rewrite <- Hcnt0.
    split; [lia|].                                    (* 1 <= len <= 15 *)
    split; [lia|].                                    (* huff in range *)
    split; [rewrite Hoffmn; lia|].                    (* window start *)
    split; [rewrite Hoffmn; lia|].                    (* window end *)
    split.
    { intros l Hl.
      destruct (Z.ltb_spec l mn) as [H1|H1]; [apply Hmnz; lia|].
      destruct (Z.eqb_spec l mn) as [->|H2]; [rewrite Hoffmn; lia|reflexivity]. }
    split; [rewrite zrev_zero; lia|].                 (* position link: 0 = 0 *)
    split.
    { (* nothing is claimed at position 0 *)
      intros j Hj Hu. exfalso.
      pose proof (zrev_nonneg (Z.to_nat r) j).
      pose proof (pow2_pos_z (15 - r) ltac:(lia)). nia. }
    left. repeat split; lia.
Qed.

(** [PreEmpty] hands the table back as a variable, so the theorem cannot see
    the two entries [it_pre] wrote unless the shape is recovered from the
    equation.  ([inftrees.c:110-118]: the [max == 0] arm writes two
    invalid-code markers and returns [*bits = 1].) *)
Lemma it_pre_empty_shape : forall ty lens codes root0 t0 t,
  it_pre ty lens codes root0 t0 = PreEmpty t ->
  t = tset (tset t0 0 (mkCodeT 64 1 0)) 1 (mkCodeT 64 1 0).
Proof.
  intros ty lens codes root0 t0 t H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [injection H as <-; reflexivity|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|discriminate H].
  destruct (it_incomplete ty lft
              (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)));
    [discriminate H|].
  match type of H with
  | (if ?b then _ else _) = _ => destruct b
  end; discriminate H.
Qed.

(** THE THEOREM, in lenext-repair's shape and in the stronger [1 <=] form. *)
Theorem it_covers_root_pos : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  forall i, 0 <= i < 2 ^ (o_bits out) -> 1 <= c_bits (o_tbl out i) <= o_bits out.
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hmodel Hret i Hi.
  unfold it_model in Hmodel.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - (* PreErr *) injection Hmodel as <-. cbn in Hret. lia.
  - (* PreEmpty: the [max = 0] arm, two markers at 0 and 1, [*bits = 1] *)
    rewrite (it_pre_empty_shape ty lens codes root0 t0 temp Hpre) in Hmodel.
    injection Hmodel as <-. cbn in Hi |- *.
    change (2 ^ 1) with 2 in Hi.
    destruct (Z.eq_dec i 1) as [->|H1].
    + rewrite tset_same, bits_mkCodeT by lia. lia.
    + rewrite tset_other by lia.
      assert (Hi0 : i = 0) by lia. rewrite Hi0.
      rewrite tset_same, bits_mkCodeT by lia. lia.
  - (* PreOver *) injection Hmodel as <-. cbn in Hret. lia.
  - (* PreGo *)
    destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
      as [Hctx Hinv].
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop;
      try discriminate Hmodel;
      injection Hmodel as <-;
      (* ItOverflow returns 1, so [o_ret = 0] kills it; ItBreak is the theorem *)
      try (cbn in Hret; lia);
      try (cbn in Hi |- *;
           apply (cov_loop (S (Z.to_nat codes)) c (sw_cnt lens codes) st st'
                    Hctx Hinv Hloop); exact Hi).
Qed.

Corollary it_covers_root : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  TblBitsPosBelow (o_bits out) (o_tbl out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hmodel Hret i Hi.
  pose proof (it_covers_root_pos ty lens codes root0 t0 out
                Hcodes Hlens Hroot0 Hmodel Hret i Hi). lia.
Qed.

(** ** 10.  AN INSTANTIATION WITNESS

    rt-scout's gate, and it is the right one: a theorem whose premises no real
    call satisfies reports [Closed under the global context] forever and reads as
    progress.  (That is not hypothetical for this lane — my own [CtxRel] was
    unsatisfiable at the CODES call type and four theorems over it were vacuous
    there.)  So the coverage theorem gets a witness that it APPLIES: a concrete
    accepted call, its premises discharged, and the conclusion non-vacuous
    because the region it quantifies is inhabited and both entries are checked.

    The call: a two-symbol complete DISTS code, both symbols one bit.  The model
    returns [o_ret = 0], [o_bits = 1], [o_used = 2], and both root entries carry
    [c_bits = 1]. *)

Definition lens_two_ones : zarr := zlist [1;1].

Example it_covers_root_instantiated :
  exists out,
    it_model CT_DISTS lens_two_ones 2 5 tnone = Some out
    /\ o_ret out = 0
    /\ o_bits out = 1
    /\ (forall i, 0 <= i < 2 -> 1 <= c_bits (o_tbl out i)).
Proof.
  assert (H2 : 0 <= 2) by lia.
  assert (Hr5 : 1 <= 5 <= 15) by lia.
  assert (Hlens : forall i, 0 <= i < 2 -> 0 <= lens_two_ones i <= 15).
  { (* two registered traps in three lines: this Rocq build rejects [as [->|->]]
       in a disjunctive intro pattern, and reducing the COMPARISON (cbn/vm_compute
       on [0 <= _ <= 15]) leaves [lia] a shape it cannot read.  Reduce the
       ARGUMENT by an equation instead. *)
    intros i Hi. assert (Hd : i = 0 \/ i = 1) by lia.
    destruct Hd as [H0|H1].
    - rewrite H0. assert (E0 : lens_two_ones 0 = 1) by reflexivity.
      rewrite E0. lia.
    - rewrite H1. assert (E1 : lens_two_ones 1 = 1) by reflexivity.
      rewrite E1. lia. }
  destruct (it_model CT_DISTS lens_two_ones 2 5 tnone) as [out|] eqn:E;
    [|vm_compute in E; discriminate].
  exists out. split; [reflexivity|].
  assert (Hret : o_ret out = 0)
    by (vm_compute in E; injection E as E'; rewrite <- E'; reflexivity).
  split; [exact Hret|].
  assert (Hbits : o_bits out = 1)
    by (vm_compute in E; injection E as E'; rewrite <- E'; reflexivity).
  split; [exact Hbits|].
  intros i Hi.
  apply (it_covers_root_pos CT_DISTS lens_two_ones 2 5 tnone out H2 Hlens Hr5 E Hret i).
  rewrite Hbits. change (2 ^ 1) with 2. exact Hi.
Qed.

Set Printing Depth 10000000000.
Print Assumptions cov_step_short.
Print Assumptions cov_step_long.
Print Assumptions pos_advance.
Print Assumptions it_mass_zero_inv.
Print Assumptions cov_next_window.
Print Assumptions cov_exhausted.
Print Assumptions offs_top.
Print Assumptions cov_after_fill.
Print Assumptions cov_step_cont.
Print Assumptions cov_step_break.
Print Assumptions cov_loop.
Print Assumptions cov_pre.
Print Assumptions it_covers_root_pos.
Print Assumptions it_covers_root.
Print Assumptions it_covers_root_instantiated.
