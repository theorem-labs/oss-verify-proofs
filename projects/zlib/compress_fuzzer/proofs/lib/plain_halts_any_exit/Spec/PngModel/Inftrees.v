(** * Spec.PngModel.Inftrees — transcription of zlib-1.3.1's [inflate_table].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.

    Source: [materials/zlib-1.3.1/inftrees.c] (in-container
    [/harness/problem/materials/zlib-1.3.1/inftrees.c]), the whole file.
    This is a BUG-FOR-BUG transcription: it reproduces zlib's exact
    two-level table layout, its [ENOUGH_LENS = 852] / [ENOUGH_DISTS = 592]
    budgets, its acceptance of one-symbol incomplete DISTS codes, and the
    deliberately-invalid [lext[29] = 203] / [lext[30] = 77] entries — NOT
    an RFC-1951 idealisation.  Where the C has a cast, the transcription
    applies the corresponding truncation ([u8]/[u16] from [Base]); where
    the C has a loop, the transcription is a [nat]-fuelled [Fixpoint] whose
    fuel is a static bound read off the same loop.

    Structure, chosen so a machine-level walk can cut where the C cuts
    (c5-invariants.md §3.2):

    - [it_pre]  — everything before the [for(;;)]: the two counting loops,
      the max/min/root clamping, the degenerate [max = 0] return, the
      Kraft over/under-subscription check, the offset prefix loop, the
      symbol sort, and the per-type [base]/[extra]/[match] selection.
      Returns either an early result or a frozen [ItCtx] (loop-invariant
      data) plus the initial [ItSt] (loop-carried state).
    - [it_step] — ONE trip of the [for(;;)], as a total function
      [ItCtx -> ItSt -> ItStep].  This is the unit the fill-loop invariant
      is stated against: the machine at the loop head after [k] trips
      carries [it_iter k].
    - [it_finish] — the incomplete-code fixup and the return parameters.

    Out-of-range reads.  [x_base]/[x_extra] are indexed by
    [work[sym] - match], and [x_lens] by [work[sym]].  For every call this
    driver makes these stay in range (LENS: [work[sym] <= 287], so
    [work[sym] - 257 <= 30 < 31]; DISTS: [work[sym] <= 31 < 32]; CODES:
    [work[sym] <= 18], so [work[sym] + 1 < 20 = match] always holds and
    [base]/[extra] — which the C aliases to [work] itself! — are never
    consulted).  [it_wf] below records the hypotheses that make this so;
    the [zarr] representation returns 0 outside a literal table rather
    than being undefined, so the model is total either way.

    Validated against the delivered binary: see
    [a working folder] (native oracle + qemu GDB-RSP dumps of
    [/harness/reference_binary]). *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
(* [&&]/[||] appear in [if] conditions, where no expected type opens
   [bool_scope] for us; neither notation collides with [Z_scope]. *)
Local Open Scope bool_scope.

(** ** Constants *)

(** [inftrees.h:49-51].  Found by exhaustive search (zlib's
    [examples/enough.c]) for root table sizes 9 and 6; hard-coded here
    because the binary hard-codes them. *)
Definition ENOUGH_LENS  : Z := 852.
Definition ENOUGH_DISTS : Z := 592.

(** [inftrees.c:35] [#define MAXBITS 15]. *)
Definition MAXBITS : Z := 15.

(** [codetype] ([inftrees.h:56-60]). *)
Definition CT_CODES : Z := 0.
Definition CT_LENS  : Z := 1.
Definition CT_DISTS : Z := 2.

(** The four static tables, [inftrees.c:57-71].  [lext[29] = 203] and
    [lext[30] = 77] are zlib's deliberate garbage for the two unused
    length symbols 286/287: they make the decoder reject rather than
    read past the table.  Transcribed verbatim. *)
Definition lbase_l : list Z :=
  [3;4;5;6;7;8;9;10;11;13;15;17;19;23;27;31;
   35;43;51;59;67;83;99;115;131;163;195;227;258;0;0].
Definition lbase : zarr := zlist lbase_l.
Definition lext_l : list Z :=
  [16;16;16;16;16;16;16;16;17;17;17;17;18;18;18;18;
   19;19;19;19;20;20;20;20;21;21;21;21;16;203;77].
Definition lext : zarr := zlist lext_l.
Definition dbase_l : list Z :=
  [1;2;3;4;5;7;9;13;17;25;33;49;65;97;129;193;
   257;385;513;769;1025;1537;2049;3073;4097;6145;
   8193;12289;16385;24577;0;0].
Definition dbase : zarr := zlist dbase_l.
Definition dext_l : list Z :=
  [16;16;16;16;17;17;18;18;19;19;20;20;21;21;22;22;
   23;23;24;24;25;25;26;26;27;27;
   28;28;29;29;64;64].
Definition dext : zarr := zlist dext_l.

(** The ENOUGH check, [inftrees.c:196-198] and [:257-259].

    NAME TRAP, two of them.  (i) This is a BOOLEAN TEST that fires when the
    table has grown TOO BIG -- [it_enough ty used = true] means "not
    enough room", the opposite of what the name reads as.  (ii) It has no
    [CT_CODES] disjunct at all, so for CODES it is IDENTICALLY FALSE: there
    is no size guard in the C on that path.  zlib relies on the caller
    passing [codes = 19], which is why [it_wf] carries
    [ty = CT_CODES /\ codes <= 19] as a caller obligation.  Any invariant
    wanting a table-size bound must therefore be TYPE-DEPENDENT -- 852 for
    LENS, 592 for DISTS, and for CODES nothing from the guard.  A uniform
    [s_used <= nT] would paper over a real bug-for-bug feature. *)
Definition it_enough (ty used : Z) : bool :=
  ((Z.eqb ty CT_LENS)  && (Z.ltb ENOUGH_LENS  used)) ||
  ((Z.eqb ty CT_DISTS) && (Z.ltb ENOUGH_DISTS used)).

(** ** Pre-loop phases *)

(** [inftrees.c:103-104]: [for (sym = 0; sym < codes; sym++) count[lens[sym]]++].
    The caller guarantees [lens[sym] <= MAXBITS]; see [it_wf]. *)
Fixpoint it_count (n : nat) (i : Z) (lens cnt : zarr) : zarr :=
  match n with
  | O => cnt
  | S k => it_count k (i + 1) lens (zset cnt (lens i) (cnt (lens i) + 1))
  end.

(** [inftrees.c:108-109]: [for (max = MAXBITS; max >= 1; max--) if (count[max] != 0) break].
    Falls out of the loop at 0 when every count is zero. *)
Fixpoint it_findmax (n : nat) (m : Z) (cnt : zarr) : Z :=
  match n with
  | O => 0
  | S k => if Z.eqb (cnt m) 0 then it_findmax k (m - 1) cnt else m
  end.

(** [inftrees.c:120-121]: [for (min = 1; min < max; min++) if (count[min] != 0) break].
    Ends at [max] if no shorter length occurs.

    FUEL BOUNDARY (WP-5 pilot, 2026-08-16).  The fuel below is 16, so the
    scan can reach index 16 -- one past the [1..15] that a fold over the
    length counts sees.  A bridge to a fold-shaped minimum therefore needs
    the side condition [mx <= 16], NOT [mx <= 15]: the two disagree
    exactly when [mx >= 17] and [cnt 1..15] are all zero and
    [cnt 16 <> 0].  Every real call site is safe, because
    [mx = it_findmax ... <= MAXBITS = 15], but the bridge lemma must carry
    the hypothesis. *)
Fixpoint it_findmin (n : nat) (m mx : Z) (cnt : zarr) : Z :=
  match n with
  | O => mx
  | S k =>
      if Z.geb m mx then mx
      else if Z.eqb (cnt m) 0 then it_findmin k (m + 1) mx cnt else m
  end.

(** [inftrees.c:125-130]: the Kraft counter.  [None] is the C's
    [return -1] on an over-subscribed set; [Some left] is the residual
    (positive means incomplete). *)
Fixpoint it_kraft (n : nat) (len left : Z) (cnt : zarr) : option Z :=
  match n with
  | O => Some left
  | S k =>
      let l := left * 2 - cnt len in
      if Z.ltb l 0 then None else it_kraft k (len + 1) l cnt
  end.

(** [inftrees.c:131-132]: [if (left > 0 && (type == CODES || max != 1))
    return -1].  zlib ACCEPTS one kind of incomplete code -- a LENS/DISTS
    set whose longest code is a single bit, i.e. the one-or-zero-symbol
    distance code -- and rejects every other incomplete set.  Named rather
    than left inline in [it_pre] because it is the whole content of the
    Kraft bridge's accept/reject obligation; naming it is the difference
    between a two-lemma bridge and one that must reason about all of
    [it_pre].

    DO NOT INLINE THIS AGAIN, and do not "simplify" the expression.  WP-5's
    phase-PC walk proves that the machine takes the reject branch exactly
    when this boolean is true, against a structurally identical
    [it_incomplete_bad]; the two are pinned to each other.  If the
    definitions ever drift, that walk breaks loudly rather than the model
    and the machine silently disagreeing -- which is the good failure mode,
    but only as long as the expression stays a named, stable thing. *)
Definition it_incomplete (ty lft mx : Z) : bool :=
  (Z.ltb 0 lft) && ((Z.eqb ty CT_CODES) || negb (Z.eqb mx 1)).

(** [inftrees.c:134-136]: [offs[1] = 0; for (len = 1; len < MAXBITS; len++)
    offs[len+1] = offs[len] + count[len]]. *)
Fixpoint it_offs (n : nat) (len : Z) (cnt offs : zarr) : zarr :=
  match n with
  | O => offs
  | S k => it_offs k (len + 1) cnt (zset offs (len + 1) (offs len + cnt len))
  end.

(** [inftrees.c:139-140]: [for (sym = 0; sym < codes; sym++)
    if (lens[sym] != 0) work[offs[lens[sym]]++] = sym].
    Note the C's post-increment: the OLD [offs] value indexes [work]. *)
Fixpoint it_sort (n : nat) (i : Z) (lens offs work : zarr) : zarr * zarr :=
  match n with
  | O => (offs, work)
  | S k =>
      let l := lens i in
      if Z.eqb l 0 then it_sort k (i + 1) lens offs work
      else it_sort k (i + 1) lens (zset offs l (offs l + 1)) (zset work (offs l) i)
  end.

(** ** Loop context and state *)

(** Loop-invariant data: fixed by [it_pre], read but never written by the
    [for(;;)] body. *)
Record ItCtx : Type := mkItCtx {
  x_type  : Z;     (** [type]: CT_CODES / CT_LENS / CT_DISTS *)
  x_codes : Z;     (** [codes] *)
  x_lens  : zarr;  (** the caller's [lens[]] *)
  x_root  : Z;     (** [root], after both clampings *)
  x_max   : Z;     (** [max] *)
  x_mask  : Z;     (** [mask = (1 << root) - 1] *)
  x_work  : zarr;  (** the sorted symbol array *)
  x_base  : zarr;  (** [base]  ([lbase] / [dbase] / aliased to [work]) *)
  x_extra : zarr;  (** [extra] ([lext]  / [dext]  / aliased to [work]) *)
  x_match : Z      (** [match]: 20 / 257 / 0 *)
}.

(** Loop-carried state.  [s_next] is the C's [next] pointer expressed as an
    OFFSET from [*table] in [code] units, so every table index in the model
    is absolute and the C's [ ( *table)[low] ] is simply index [low].
    [s_min] is the
    C's reuse of [min] as "1 << curr of the table currently being filled"
    ([inftrees.c:225] "here min is 1 << curr"). *)
Record ItSt : Type := mkItSt {
  s_huff  : Z;
  s_sym   : Z;
  s_len   : Z;
  s_next  : Z;
  s_curr  : Z;
  s_drop  : Z;
  s_low   : Z;
  s_used  : Z;   (** NAME TRAP: ALLOCATED capacity, not entries WRITTEN.
                        It starts at [2^root] with nothing written and grows
                        by [2^curr] when a sub-table is RESERVED, which later
                        trips then fill.  An invariant quantified over
                        [[0, s_used)] is therefore claiming something about
                        unwritten memory -- and since [it_pre] starts the
                        table at the caller's arbitrary [t0], that claim is
                        false at trip 0.  This cost a drafted L3 invariant
                        conjunct on 2026-08-16.  The name is the C's
                        ([inftrees.c]'s [used]) and is kept for fidelity;
                        the warning is here instead. *)
  s_min   : Z;
  s_count : zarr;
  s_tbl   : ztbl
}.

Inductive ItStep : Type :=
| ItCont     (st : ItSt)   (** fell through to the next trip *)
| ItBreak    (st : ItSt)   (** [inftrees.c:221] [break] *)
| ItOverflow (t : ztbl).   (** [inftrees.c:239] [return 1]; [t] = table as dirtied *)

(** ** One trip of the main loop *)

(** [inftrees.c:203-215]: the entry to duplicate. *)
Definition it_here (c : ItCtx) (st : ItSt) : Code :=
  let w := x_work c (s_sym st) in
  let b := s_len st - s_drop st in
  if Z.ltb (w + 1) (x_match c) then mkCodeT 0 b w
  else if Z.leb (x_match c) w
       then mkCodeT (x_extra c (w - x_match c)) b (x_base c (w - x_match c))
       else mkCodeT (32 + 64) b 0.

(** [inftrees.c:218-223]:
<<
      incr = 1U << (len - drop);  fill = 1U << curr;  min = fill;
      do { fill -= incr; next[(huff >> drop) + fill] = here; } while (fill != 0);
>>
    [n] is the trip count [fill / incr = 2^(curr - (len - drop))]; the
    recursion writes index [n-1] first, matching the C's descending [fill].
    All writes store the SAME entry at pairwise-distinct indices, so the
    result is also characterised pointwise: see [it_fill_hit] /
    [it_fill_miss] for the two directions a walk uses, and [it_fill_get]
    for the single divisibility-flavoured equation that a cross-model
    bridge wants (WP-5 states [g_fill] in that form). *)
Fixpoint it_fill (n : nat) (t : ztbl) (bi incr : Z) (h : Code) : ztbl :=
  match n with
  | O => t
  | S k => it_fill k (tset t (bi + Z.of_nat k * incr) h) bi incr h
  end.

(** [inftrees.c:226-228]: [incr = 1U << (len - 1); while (huff & incr) incr >>= 1].
    Fuel 17 > MAXBITS + 1, so the scan always reaches [incr = 0], at which
    point [huff & 0 = 0] stops it. *)
Fixpoint it_shift_down (n : nat) (huff incr : Z) : Z :=
  match n with
  | O => incr
  | S k => if Z.eqb (Z.land huff incr) 0 then incr
           else it_shift_down k huff (Z.shiftr incr 1)
  end.

(** [inftrees.c:226-233]: the bit-reversed increment of the [len]-bit code. *)
Definition it_rev_incr (huff len : Z) : Z :=
  let incr := it_shift_down 17%nat huff (Z.shiftl 1 (len - 1)) in
  if Z.eqb incr 0 then 0 else Z.land huff (incr - 1) + incr.

(** [inftrees.c:249-255]: sizing the next sub-table by looking ahead in the
    (already decremented) length counts.  Fuel 16 > MAXBITS. *)
Fixpoint it_subsz (n : nat) (cnt : zarr) (drop mx curr left : Z) : Z :=
  match n with
  | O => curr
  | S k =>
      if Z.ltb (curr + drop) mx then
        let l := left - cnt (curr + drop) in
        if Z.leb l 0 then curr else it_subsz k cnt drop mx (curr + 1) (l * 2)
      else curr
  end.

(** One trip of [inftrees.c:201-270]. *)
Definition it_step (c : ItCtx) (st : ItSt) : ItStep :=
  let here  := it_here c st in
  let incr  := Z.shiftl 1 (s_len st - s_drop st) in
  let fill0 := Z.shiftl 1 (s_curr st) in
  (* :221-223 replicate *)
  let tbl1  := it_fill (Z.to_nat (fill0 / incr)) (s_tbl st)
                       (s_next st + Z.shiftr (s_huff st) (s_drop st)) incr here in
  (* :226-233 backwards increment *)
  let huff1 := it_rev_incr (s_huff st) (s_len st) in
  (* :236-240 next symbol, update count, len *)
  let sym1  := s_sym st + 1 in
  let cnt1  := zset (s_count st) (s_len st) (s_count st (s_len st) - 1) in
  let hit0  := Z.eqb (cnt1 (s_len st)) 0 in
  let st1   := {| s_huff := huff1; s_sym := sym1; s_len := s_len st;
                  s_next := s_next st; s_curr := s_curr st; s_drop := s_drop st;
                  s_low := s_low st; s_used := s_used st; s_min := fill0;
                  s_count := cnt1; s_tbl := tbl1 |} in
  if hit0 && Z.eqb (s_len st) (x_max c) then ItBreak st1
  else
    let len1 := if hit0 then x_lens c (x_work c sym1) else s_len st in
    (* :243-268 create new sub-table if needed *)
    if (Z.ltb (x_root c) len1)
       && negb (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) then
      let drop' := if Z.eqb (s_drop st) 0 then x_root c else s_drop st in
      let next' := s_next st + fill0 in
      let curr0 := len1 - drop' in
      let curr' := it_subsz 16%nat cnt1 drop' (x_max c) curr0 (Z.shiftl 1 curr0) in
      let used' := s_used st + Z.shiftl 1 curr' in
      if it_enough (x_type c) used' then ItOverflow tbl1
      else
        let low'  := Z.land huff1 (x_mask c) in
        let tbl2  := tset tbl1 low' (mkCodeT curr' (x_root c) next') in
        ItCont {| s_huff := huff1; s_sym := sym1; s_len := len1;
                  s_next := next'; s_curr := curr'; s_drop := drop';
                  s_low := low'; s_used := used'; s_min := fill0;
                  s_count := cnt1; s_tbl := tbl2 |}
    else
      ItCont {| s_huff := huff1; s_sym := sym1; s_len := len1;
                s_next := s_next st; s_curr := s_curr st; s_drop := s_drop st;
                s_low := s_low st; s_used := s_used st; s_min := fill0;
                s_count := cnt1; s_tbl := tbl1 |}.

(** The state after [k] fall-through trips — the term a machine-level
    fill-loop invariant is indexed by.  [None] once the loop has left via
    [break] or [return 1] within those [k] trips. *)
Fixpoint it_iter (k : nat) (c : ItCtx) (st : ItSt) : option ItSt :=
  match k with
  | O => Some st
  | S k' => match it_step c st with
            | ItCont st' => it_iter k' c st'
            | _ => None
            end
  end.

(** Run to the loop's exit. *)
Fixpoint it_loop (n : nat) (c : ItCtx) (st : ItSt) : option ItStep :=
  match n with
  | O => None
  | S k => match it_step c st with
           | ItCont st' => it_loop k c st'
           | r => Some r
           end
  end.

(** ** Pre-loop driver *)

Inductive ItPre : Type :=
| PreErr                      (** [return -1] ([:129] or [:132]) *)
| PreEmpty (t : ztbl)         (** the [max == 0] arm ([:110-118]) *)
| PreOver                     (** [return 1] from the initial check ([:197]) *)
| PreGo (c : ItCtx) (st : ItSt).

Definition it_pre (ty : Z) (lens : zarr) (codes root0 : Z) (t0 : ztbl) : ItPre :=
  (* :101-104 *)
  let cnt0 := it_count (Z.to_nat codes) 0 lens zzero in
  (* :107-109 *)
  let mx := it_findmax 15%nat MAXBITS cnt0 in
  let r1 := if Z.ltb mx root0 then mx else root0 in
  if Z.eqb mx 0 then
    (* :110-118: two invalid-code markers, *bits = 1, return 0 *)
    PreEmpty (tset (tset t0 0 (mkCodeT 64 1 0)) 1 (mkCodeT 64 1 0))
  else
    (* :120-122 *)
    let mn := it_findmin 16%nat 1 mx cnt0 in
    let r  := if Z.ltb r1 mn then mn else r1 in
    (* :125-132 *)
    match it_kraft 15%nat 1 1 cnt0 with
    | None => PreErr
    | Some lft =>
        if it_incomplete ty lft mx then PreErr
        else
          (* :134-140 *)
          let offs := it_offs 14%nat 1 cnt0 (zset zzero 1 0) in
          let wk   := snd (it_sort (Z.to_nat codes) 0 lens offs zzero) in
          (* :175-190 *)
          let bs := if Z.eqb ty CT_LENS then lbase
                    else if Z.eqb ty CT_DISTS then dbase else wk in
          let ex := if Z.eqb ty CT_LENS then lext
                    else if Z.eqb ty CT_DISTS then dext else wk in
          let mt := if Z.eqb ty CT_LENS then 257
                    else if Z.eqb ty CT_DISTS then 0 else 20 in
          (* :193-198 *)
          let used0 := Z.shiftl 1 r in
          if it_enough ty used0 then PreOver
          else
            PreGo {| x_type := ty; x_codes := codes; x_lens := lens;
                     x_root := r; x_max := mx; x_mask := used0 - 1;
                     x_work := wk; x_base := bs; x_extra := ex; x_match := mt |}
                  {| s_huff := 0; s_sym := 0; s_len := mn; s_next := 0;
                     s_curr := r; s_drop := 0;
                     s_low := 4294967295 (* (unsigned)(-1), :186 *);
                     s_used := used0; s_min := mn;
                     s_count := cnt0; s_tbl := t0 |}
    end.

(** [inftrees.c:272-281]: the incomplete-code fixup. *)
Definition it_finish (st : ItSt) : ztbl :=
  if Z.eqb (s_huff st) 0 then s_tbl st
  else tset (s_tbl st) (s_next st + s_huff st)
            (mkCodeT 64 (s_len st - s_drop st) 0).

(** ** The model

    The C's out-parameters, as the differential harness observes them:
    [o_ret] the return value; [o_bits] [*bits] on return (UNCHANGED on an
    error return — the C returns before [:284]); [o_used] the advance of
    [*table], i.e. [used] on success and 0 on either error return; [o_tbl]
    the table as left in memory (meaningful beyond [o_used] only as a
    record of what got dirtied). *)
Record ItOut : Type := mkItOut {
  o_ret  : Z;
  o_bits : Z;
  o_used : Z;
  o_tbl  : ztbl
}.

(** [None] means the fuel bound was hit.  Nothing in this file is
    admitted and there is no [it_terminates]: the termination ARGUMENT is
    [it_measure] / [it_step_decreases] below (every fall-through trip does
    [sym++], so [codes - sym] strictly decreases and [S codes] bounds the
    trip count).  The remaining half — "[sym] cannot reach [codes] without
    the loop having taken [ItBreak]" — needs the Kraft/count facts and
    is NOT claimed here and has no home yet: there is no
    [Spec/PngModel/InftreesThy.v].  The [ChecksumThy.v] convention is
    real, but no [Thy] file for this module has been written, so this is
    a pointer to WP-5 pilot/bridge work, not to a file.
    [it_loop_fuel_mono] lets a walk prove a bound at whatever fuel is
    convenient and transfer it to the [S (Z.to_nat codes)] the model
    uses. *)
(** INTERFACE NOTE ([t0], for bridge lanes).  [t0] is the table as it
    already sits in memory, and it is NOT always [tnone].  Only the
    [makefixed]/[fixedtables] call sites pass [tnone]; the real decoder
    call site ([Inflate.inf_table]) passes
    [fun i => t_codes (s_tab st) (k + i)] -- a SHIFTED VIEW of
    [state->codes], because the C's [*table] is [state->codes + k] and
    each of the three per-block calls starts where the previous one
    stopped.  A composite bridge stated only at [t0 = tnone] would not
    cover the decoder.  The parameter exists precisely because zlib
    [ZALLOC]s [state->codes] unzeroed and never clears it, so the entries
    a call does not write are the caller's, not zeros. *)
Definition it_model (ty : Z) (lens : zarr) (codes root0 : Z) (t0 : ztbl)
  : option ItOut :=
  match it_pre ty lens codes root0 t0 with
  | PreErr     => Some {| o_ret := -1; o_bits := root0; o_used := 0; o_tbl := t0 |}
  | PreOver    => Some {| o_ret :=  1; o_bits := root0; o_used := 0; o_tbl := t0 |}
  | PreEmpty t => Some {| o_ret :=  0; o_bits := 1;     o_used := 2; o_tbl := t  |}
  | PreGo c st =>
      match it_loop (S (Z.to_nat codes)) c st with
      | Some (ItBreak st') =>
          Some {| o_ret := 0; o_bits := x_root c;
                  o_used := s_used st'; o_tbl := it_finish st' |}
      | Some (ItOverflow t) =>
          Some {| o_ret := 1; o_bits := root0; o_used := 0; o_tbl := t |}
      | Some (ItCont _) => None   (* unreachable: [it_loop] never yields [ItCont] *)
      | None => None
      end
  end.

(** ** Well-formedness of a call

    The hypotheses [inflate_table]'s own comment demands of its caller
    ("This routine assumes, but does not check, that all of the entries in
    lens[] are in the range 0..MAXBITS"), plus the two that keep
    [base]/[extra] in range.  Every call [inflate.c] makes satisfies these;
    a machine-level walk discharges them from the caller's invariant. *)
Definition it_wf (ty : Z) (lens : zarr) (codes root0 : Z) : Prop :=
  0 < codes
  /\ (forall i, 0 <= i < codes -> 0 <= lens i <= MAXBITS)
  /\ 1 <= root0 <= MAXBITS
  /\ (ty = CT_CODES /\ codes <= 19
      \/ ty = CT_LENS /\ codes <= 288
      \/ ty = CT_DISTS /\ codes <= 32).


(** ** What [it_count] computes — the transcription half of the histogram
       obligation

    [Spec/PngModel/InftreesBridge.v] states [CountsOf] as a hypothesis and
    routes the proof here, correctly: what [it_count] tallies is a fact
    about the TRANSCRIPTION, not about the spec.

    The obligation is discharged in two pieces along the C13 layering line,
    because [Huff.count_len] lives in the frozen spec and this file must
    not import it.  Everything below is the transcription-side half, stated
    purely over [zarr]s.  The remaining step -- that [zcount] over [zlens]
    is [count_len] -- is a short list induction, and it is DONE: it is
    [InftreesBridge.zcount_zlens_count_len], whose inductive step is
    [zcount_zlens_cons] below composed with [count_occ]'s cons behaviour.
    So the [CountsOf] obligation is fully discharged and
    [InftreesBridge.it_pre_go_prefix_free] carries no histogram hypothesis
    at all.

    Worth knowing when reading [zcount_zlens_tail]: it is what pins the
    TRAVERSAL DIRECTION.  A backwards walk produces the same histogram, so
    the order of the length list is invisible through [CountsOf] and no
    test can catch a reversed traversal (proved, not assumed:
    [InftreesBridge.count_len_rev] / [histogram_order_blind]).  Direction
    is pinned here or nowhere.

    Note the shape: [it_count] ADDS to whatever the accumulator held, so
    the characterisation is [cnt b + zcount ...] rather than an equality
    with the count.  [it_pre] passes [zzero], hence [it_count_zzero]. *)

(** The number of indices in [[i, i + n)] whose length is [b]. *)
Fixpoint zcount (n : nat) (i : Z) (lens : zarr) (b : Z) : Z :=
  match n with
  | O => 0
  | S k => (if Z.eqb (lens i) b then 1 else 0) + zcount k (i + 1) lens b
  end.

Lemma it_count_spec :
  forall n i lens cnt b,
    it_count n i lens cnt b = cnt b + zcount n i lens b.
Proof.
  induction n as [|n IH]; intros i lens cnt b; cbn [it_count zcount].
  - lia.
  - rewrite IH. unfold zset.
    destruct (Z.eqb_spec b (lens i)) as [Hb|Hb].
    + subst b. rewrite Z.eqb_refl. lia.
    + destruct (Z.eqb_spec (lens i) b) as [He|He]; [congruence|lia].
Qed.

Corollary it_count_zzero :
  forall n lens b, it_count n 0 lens zzero b = zcount n 0 lens b.
Proof. intros; rewrite it_count_spec; reflexivity. Qed.

Lemma zcount_ext :
  forall n i f g b,
    (forall j, i <= j < i + Z.of_nat n -> f j = g j) ->
    zcount n i f b = zcount n i g b.
Proof.
  induction n as [|n IH]; intros i f g b H; cbn [zcount]; [reflexivity|].
  rewrite (H i) by lia.
  f_equal. apply IH. intros j Hj. apply H. lia.
Qed.

(** The [zarr] view of a list of code lengths -- the representation the
    spec side counts over.  Out of range it reads 0, i.e. "absent", the
    same convention [it_count] itself uses. *)
Definition zlens (l : list nat) : zarr :=
  fun i => Z.of_nat (nth (Z.to_nat i) l 0%nat).

(** Walking a cons cell from index [i+1] is walking the tail from [i]. *)
Lemma zcount_zlens_tail :
  forall n i x l b,
    0 <= i ->
    zcount n (i + 1) (zlens (x :: l)) b = zcount n i (zlens l) b.
Proof.
  induction n as [|n IH]; intros i x l b Hi; cbn [zcount]; [reflexivity|].
  assert (Hz : zlens (x :: l) (i + 1) = zlens l i).
  { unfold zlens. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    now cbn [nth]. }
  rewrite Hz. f_equal. apply IH. lia.
Qed.

(** Peeling one symbol: the inductive step the bridge's [count_len] proof
    needs, with the index arithmetic already done. *)
Lemma zcount_zlens_cons :
  forall x l b,
    zcount (length (x :: l)) 0 (zlens (x :: l)) b
    = (if Z.eqb (Z.of_nat x) b then 1 else 0) + zcount (length l) 0 (zlens l) b.
Proof.
  intros x l b. cbn [length zcount].
  assert (H0 : zlens (x :: l) 0 = Z.of_nat x) by reflexivity.
  rewrite H0. f_equal.
  apply (zcount_zlens_tail (length l) 0 x l b). lia.
Qed.


(** ** Positive code widths — the carried fact LT's stalled arms need

    LT's LEN / LENEXT / DIST / DISTEXT arms are blocked on one thing: a
    decode that returns the right symbol having consumed ZERO bits cannot
    be ruled out, and the termination measure is a bit budget.  What rules
    it out is that every entry [it_model] writes has [1 <= c_bits].

    HONEST SCOPE, because the arbiter took this obligation on the grounds
    that LT is its only consumer and that was only half right.  Every
    [c_bits] written is one of [s_len st - s_drop st] (three sites),
    [x_root c] (the sub-table pointer, [inftrees.c:266]), or the literal 1
    (the [max == 0] markers).  So the general statement needs
    [1 <= s_len st - s_drop st] at every loop state, which is exactly
    **L3's fill-loop invariant, currently UNOWNED**.  It is NOT
    independently provable here, and saying otherwise would be the
    plan-label mistake again in a different costume.

    [TblBitsPos] is therefore a HYPOTHESIS, in the [lcode_len_bounded]
    style: state it, consume it, discharge it when L3 lands.  LT can prove
    its consequence (a decode consumes at least one bit) against the
    hypothesis today and lose nothing when it becomes a theorem.  The two
    scan lemmas below are the pieces that genuinely do not need the loop,
    and they are where a discharge would start. *)

(** Every entry below [n] has a positive code width. *)
Definition TblBitsPos (t : ztbl) (n : Z) : Prop :=
  forall i, 0 <= i < n -> 1 <= c_bits (t i).

(** When [it_findmax] finds a code at all, it finds one of width at least
    1.  The fuel/start relation is what keeps the scan off bucket 0 — the
    same phenomenon the bridge records as [it_kraft_never_reads_cnt0], on
    the other loop. *)
Lemma it_findmax_pos :
  forall n m cnt,
    Z.of_nat n <= m -> it_findmax n m cnt <> 0 -> 1 <= it_findmax n m cnt.
Proof.
  induction n as [|n IH]; intros m cnt Hnm H; cbn [it_findmax] in *.
  - congruence.
  - rewrite Nat2Z.inj_succ in Hnm.
    destruct (Z.eqb (cnt m) 0).
    + apply IH; [lia | exact H].
    + lia.
Qed.

Lemma it_findmin_pos :
  forall n m mx cnt, 1 <= m -> 1 <= mx -> 1 <= it_findmin n m mx cnt.
Proof.
  induction n as [|n IH]; intros m mx cnt Hm Hmx; cbn [it_findmin]; [lia|].
  destruct (Z.geb_spec m mx) as [_|_]; [lia|].
  destruct (Z.eqb (cnt m) 0); [apply IH; lia | lia].
Qed.


(** The root width the loop starts from is positive.

    This is the residual precondition wp5-pc flagged on the sub-table
    POINTER case: the pointer entry takes its width from [root], not from
    [len - drop], so [1 <= c_bits] for pointers needs [1 <= root]
    separately.  They report it is not projectable from the G-lane's
    invariant, which carries [drop = 0 \/ drop = root] and [drop < len] but
    no lower bound on [root] itself.

    It IS derivable here, because [it_pre] computes the root and this file
    can see how: [r = max (min mx root0) mn], with [1 <= root0] from
    [it_wf], [1 <= mx] from the branch condition that reached [PreGo], and
    [1 <= mn] because [it_findmin] starts at 1.  So the obligation does not
    have to travel as a hypothesis; it is discharged at the source. *)

Lemma root_clamp_pos :
  forall mx root0 mn,
    1 <= mx -> 1 <= root0 -> 1 <= mn ->
    1 <= (if Z.ltb (if Z.ltb mx root0 then mx else root0) mn
          then mn else (if Z.ltb mx root0 then mx else root0)).
Proof.
  intros mx root0 mn Hmx Hr Hmn.
  destruct (Z.ltb mx root0) eqn:E1; cbn;
    [ destruct (Z.ltb mx mn) | destruct (Z.ltb root0 mn) ]; lia.
Qed.

Lemma it_pre_root_pos :
  forall ty lens codes root0 t0 c st,
    1 <= root0 ->
    it_pre ty lens codes root0 t0 = PreGo c st ->
    1 <= x_root c.
Proof.
  intros ty lens codes root0 t0 c st Hr H.
  unfold it_pre in H.
  destruct (Z.eqb_spec (it_findmax 15%nat MAXBITS
                          (it_count (Z.to_nat codes) 0 lens zzero)) 0) as [Hz|Hz];
    [discriminate|].
  assert (Hmx : 1 <= it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)).
  { apply it_findmax_pos; [cbn; unfold MAXBITS; lia | exact Hz]. }
  assert (Hmn : 1 <= it_findmin 16%nat 1
                      (it_findmax 15%nat MAXBITS
                         (it_count (Z.to_nat codes) 0 lens zzero))
                      (it_count (Z.to_nat codes) 0 lens zzero)).
  { apply it_findmin_pos; lia. }
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|] eqn:Hk; [|discriminate].
  destruct (it_incomplete ty lft
              (it_findmax 15%nat MAXBITS
                 (it_count (Z.to_nat codes) 0 lens zzero))) eqn:Hi;
    [discriminate|].
  match type of H with
  | context[it_enough ?a ?b] => destruct (it_enough a b) eqn:He
  end; [discriminate|].
  inversion H; subst; cbn [x_root].
  apply root_clamp_pos; assumption.
Qed.


(** ** Reading an [ItPre] without destructing it

    Placement ruling (arbiter, 2026-08-16): these belong here, beside
    [it_sym_of], not in a consumer's file.  [ItPre] is this file's type and
    a projection over it is this file's business; and wp5-pc needs it in a
    spec-side-only position, which [Inftrees.v] is.

    They exist for the reason [it_sym_of] does, now measured: inverting an
    [it_pre] result costs about 23 s of [coqc] all by itself (an 11-field
    state record times a 10-field context record over the let-inlined
    body), where reading a field through a projection costs nothing.  That
    is convention C23, and this is the C16 discipline — do not destruct the
    large record at all — applied to [ItPre].

    Each takes a default for the arms that carry no such field, so the
    projections are total and no [match] escapes into a consumer's goal. *)

Definition pre_ctx_of (r : ItPre) (d : ItCtx) : ItCtx :=
  match r with
  | PreGo c _ => c
  | _ => d
  end.

Definition pre_st_of (r : ItPre) (d : ItSt) : ItSt :=
  match r with
  | PreGo _ st => st
  | _ => d
  end.

Definition pre_tbl_of (r : ItPre) (d : ztbl) : ztbl :=
  match r with
  | PreEmpty t => t
  | PreGo _ st => s_tbl st
  | _ => d
  end.

(** [pre_root_of] is the field the pointer-width obligation is about, so it
    gets its own name rather than being spelled [x_root (pre_ctx_of ...)]
    at every use site. *)
Definition pre_root_of (r : ItPre) (d : Z) : Z :=
  match r with
  | PreGo c _ => x_root c
  | _ => d
  end.

Lemma pre_ctx_of_go : forall c st d, pre_ctx_of (PreGo c st) d = c.
Proof. reflexivity. Qed.

Lemma pre_st_of_go : forall c st d, pre_st_of (PreGo c st) d = st.
Proof. reflexivity. Qed.

Lemma pre_root_of_go : forall c st d, pre_root_of (PreGo c st) d = x_root c.
Proof. reflexivity. Qed.

(** [it_pre_root_pos] restated through the projection, so a consumer never
    has to name [c] and never has to invert. *)
Corollary it_pre_root_of_pos :
  forall ty lens codes root0 t0 c st,
    1 <= root0 ->
    it_pre ty lens codes root0 t0 = PreGo c st ->
    1 <= pre_root_of (it_pre ty lens codes root0 t0) 1.
Proof.
  intros ty lens codes root0 t0 c st Hr H.
  rewrite H, pre_root_of_go.
  exact (it_pre_root_pos ty lens codes root0 t0 c st Hr H).
Qed.

(** ** Elementary facts

    Small, cheap, and used by the walk; the substantial obligations
    (termination, the table's canonical-decode property) belong to WP-5's
    pilot and bridge lanes.  There is deliberately no
    [Spec/PngModel/InftreesThy.v]: nothing has been written into one, and
    an unwritten file is not a place to route a reader. *)

(** [it_fill n t bi incr h] overwrites exactly the [n] indices
    [bi + m * incr], [m < n].  Stated as the hit/miss pair a walk uses
    directly, rather than as one divisibility-flavoured equation. *)

Lemma it_fill_miss :
  forall n t bi incr h j,
    (forall m, (m < n)%nat -> j <> bi + Z.of_nat m * incr) ->
    it_fill n t bi incr h j = t j.
Proof.
  induction n as [|n IH]; intros t bi incr h j Hmiss; cbn [it_fill].
  - reflexivity.
  - rewrite IH by (intros m Hm; apply Hmiss; lia).
    apply tset_other, Hmiss; lia.
Qed.

Lemma it_fill_hit :
  forall n t bi incr h m,
    0 < incr -> (m < n)%nat ->
    it_fill n t bi incr h (bi + Z.of_nat m * incr) = h.
Proof.
  induction n as [|n IH]; intros t bi incr h m Hincr Hm; [lia|].
  cbn [it_fill].
  destruct (Nat.eq_dec m n) as [->|Hne].
  - rewrite it_fill_miss by
      (intros k Hk Heq; assert (Z.of_nat k < Z.of_nat n) by lia; nia).
    apply tset_same.
  - apply IH; [assumption | lia].
Qed.

(** The two directions combined into the single divisibility-flavoured
    equation a cross-model bridge wants: [it_fill] rewrites exactly the
    indices in [[bi, bi + n*incr)] congruent to [bi] modulo [incr], and
    leaves every other index alone.  WP-5's [g_fill] is stated in this
    shape, so the bridge is a rewrite rather than an induction. *)
Lemma it_fill_get :
  forall n t bi incr h j,
    0 < incr ->
    it_fill n t bi incr h j =
      (if (Z.leb bi j) && (Z.ltb j (bi + Z.of_nat n * incr))
          && (Z.eqb ((j - bi) mod incr) 0)
       then h else t j).
Proof.
  intros n t bi incr h j Hincr.
  assert (Hnn : forall m : nat, 0 <= Z.of_nat m * incr)
    by (intros m; apply Z.mul_nonneg_nonneg; [apply Nat2Z.is_nonneg | lia]).
  destruct (Z.leb_spec bi j) as [Hb|Hb]; cbn [andb].
  2:{ apply it_fill_miss; intros m Hm Heq. specialize (Hnn m). lia. }
  destruct (Z.ltb_spec j (bi + Z.of_nat n * incr)) as [Hj|Hj]; cbn [andb].
  2:{ apply it_fill_miss; intros m Hm Heq.
      assert (Z.of_nat m < Z.of_nat n) by lia. nia. }
  destruct (Z.eqb_spec ((j - bi) mod incr) 0) as [Hm0|Hm0].
  - assert (Hd : (incr | j - bi)) by (apply Z.mod_divide; lia).
    destruct Hd as [q Hq].
    assert (Hq0 : 0 <= q) by nia.
    assert (Hqn : q < Z.of_nat n) by nia.
    replace j with (bi + Z.of_nat (Z.to_nat q) * incr)
      by (rewrite Z2Nat.id by lia; lia).
    apply it_fill_hit; [assumption | lia].
  - apply it_fill_miss; intros m Hm Heq. apply Hm0. rewrite Heq.
    replace (bi + Z.of_nat m * incr - bi) with (Z.of_nat m * incr) by ring.
    apply Z.mod_mul; lia.
Qed.

(** [it_iter] composes with [it_loop]: running [k] trips then the rest is
    running the whole thing.  The bridge a walk uses to hand its loop
    invariant to the exit lemma. *)
Lemma it_iter_loop :
  forall k n c st st',
    it_iter k c st = Some st' ->
    it_loop (k + n) c st = it_loop n c st'.
Proof.
  induction k as [|k IH]; intros n c st st' H; cbn [it_iter] in H.
  - inversion H; subst. reflexivity.
  - destruct (it_step c st) eqn:Hs; try discriminate.
    cbn [Nat.add]. cbn [it_loop]. rewrite Hs. now apply IH.
Qed.

(** ** Fuel monotonicity and the loop measure

    Every [None] [it_model] can return comes from [it_loop] exhausting its
    fuel, so every downstream lemma has to rule those out.  The two facts
    that make that tractable live here, once, rather than being reinvented
    per caller.

    FUEL MONOTONICITY.  A result obtained at ANY fuel is the result at
    every larger fuel. *)
Lemma it_loop_fuel_mono :
  forall n n' c st r,
    (n <= n')%nat -> it_loop n c st = Some r -> it_loop n' c st = Some r.
Proof.
  induction n as [|n IH]; intros n' c st r Hle H; cbn [it_loop] in H;
    [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [it_loop].
  destruct (it_step c st); try exact H.
  apply IH; [lia | exact H].
Qed.

(** [it_iter] is monotone in the opposite direction: a run of [k]
    fall-through trips contains a run of every shorter length. *)
Lemma it_iter_some_le :
  forall k k' c st st',
    (k' <= k)%nat -> it_iter k c st = Some st' ->
    exists st'', it_iter k' c st = Some st''.
Proof.
  induction k as [|k IH]; intros k' c st st' Hle H.
  - assert (k' = 0)%nat by lia. subst k'. cbn [it_iter]. eauto.
  - destruct k' as [|k']; [cbn [it_iter]; eauto|].
    cbn [it_iter] in H |- *.
    destruct (it_step c st) as [st1| |]; try discriminate H.
    apply (IH k' c st1 st'); [lia | exact H].
Qed.

(** THE MEASURE the fuel abbreviates.  [inftrees.c:201]'s [for (;;)] runs
    over SYMBOLS: every fall-through trip does [sym++] ([:236]), so
    [codes - sym] strictly decreases.  Naming it fixes the shape the
    remaining termination obligation is stated against. *)
Definition it_measure (c : ItCtx) (st : ItSt) : Z := x_codes c - s_sym st.

(** The [ItStep] projection the decrease is read through.  Going via a
    projection rather than [injection] is not stylistic: [ItCont]'s
    argument is a record whose fields carry whole [it_fill] / [it_subsz]
    calls, and [injection] on that equality does not terminate in
    practice (measured: > 150 s).  [reflexivity] through a projection is
    whnf-driven and costs 0.4 s. *)
Definition it_sym_of (r : ItStep) (d : Z) : Z :=
  match r with
  | ItCont s => s_sym s
  | ItBreak s => s_sym s
  | ItOverflow _ => d
  end.

(** Both exits that carry a state carry the INCREMENTED [sym], so the
    branch analysis is uniform. *)
Lemma it_step_sym_all :
  forall c st, it_sym_of (it_step c st) (s_sym st + 1) = s_sym st + 1.
Proof.
  intros c st. unfold it_step. cbv zeta.
  repeat (match goal with
          | |- context [if ?b then _ else _] => destruct b eqn:?; cbv iota
          end); reflexivity.
Qed.

Lemma it_step_sym :
  forall c st st', it_step c st = ItCont st' -> s_sym st' = s_sym st + 1.
Proof.
  intros c st st' H. pose proof (it_step_sym_all c st) as Hs.
  rewrite H in Hs. cbn [it_sym_of] in Hs. exact Hs.
Qed.

Lemma it_step_decreases :
  forall c st st',
    it_step c st = ItCont st' -> it_measure c st' = it_measure c st - 1.
Proof.
  intros c st st' H. unfold it_measure. rewrite (it_step_sym c st st' H). lia.
Qed.

(** [it_fill] as a RANGE fact.  [it_fill_miss] is pointwise with a
    per-index side condition; a table lemma wants the window, and
    [Base]'s [tbl_eq_on] is the shape everything else composes with. *)
Lemma it_fill_tbl_eq_on :
  forall n t bi incr h lo hi,
    (forall m, (m < n)%nat -> ~ (lo <= bi + Z.of_nat m * incr < hi)) ->
    tbl_eq_on (it_fill n t bi incr h) t lo hi.
Proof.
  intros n t bi incr h lo hi Hmiss j Hj.
  apply it_fill_miss. intros m Hm Heq. apply (Hmiss m Hm). now rewrite <- Heq.
Qed.

(** ** Convenience wrappers for the differential harness

    [zarr]/[ztbl] are functions, so a test driver hands in a list and reads
    back a list. *)

Definition it_model_l (ty : Z) (lens : list Z) (root0 : Z) : option (Z * Z * Z * list Code) :=
  match it_model ty (zlist lens) (Z.of_nat (length lens)) root0 tnone with
  | None => None
  | Some o => Some (o_ret o, o_bits o, o_used o, ztbl_take (o_tbl o) (o_used o))
  end.
