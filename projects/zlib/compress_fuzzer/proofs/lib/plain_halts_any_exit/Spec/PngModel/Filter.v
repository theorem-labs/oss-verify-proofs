(** * Spec.PngModel.Filter — transcription of libpng-1.6.43's row filters.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.

    Sources ([materials/libpng-1.6.43/], in-container
    [/harness/problem/materials/libpng-1.6.43/]):

    - [pngrutil.c:3930-3946]  [png_read_filter_row_sub]
    - [pngrutil.c:3948-3962]  [png_read_filter_row_up]
    - [pngrutil.c:3964-3988]  [png_read_filter_row_avg]
    - [pngrutil.c:3990-4038]  [png_read_filter_row_paeth_1byte_pixel]
    - [pngrutil.c:4041-4102]  [png_read_filter_row_paeth_multibyte_pixel]
    - [pngrutil.c:4104-4128]  [png_init_filter_functions]
    - [pngrutil.c:4130-4145]  [png_read_filter_row]
    - [pngwutil.c:2278-2537]  [png_setup_{sub,up,avg,paeth}_row{,_only}]
    - [pngwutil.c:2548-2734]  [png_write_find_filter]
    - [pngwutil.c:1930-1975]  [png_write_start_row]'s filter-set narrowing
    - [pngwutil.c:824-831]    [png_write_IHDR]'s [do_filter] default

    ** Which variants the delivered binary reaches

    [png_init_filter_functions] ([pngrutil.c:4104]) installs
    [png_read_filter_row_paeth_1byte_pixel] when [bpp == 1] and
    [png_read_filter_row_paeth_multibyte_pixel] otherwise; BOTH are in the
    binary as local symbols (0x2623c size 0xa4 and 0x262e0 size 0xd0), so
    both are transcribed.  [PNG_FILTER_OPTIMIZATIONS] ([pngrutil.c:4118])
    is a configure-time hook for arm / intel / mips / powerpc / loongarch
    only — riscv64 has none and the binary has no such symbol, so the
    generic C above is what runs.  [PNG_USE_ABS] is defined nowhere in the
    tree, so the [? :] arms of [pa]/[pb]/[pc] are the compiled ones; they
    are numerically [abs] either way.

    ** Bug-for-bug item: two different Paeth formulations in one library

    The WRITE side ([pngwutil.c:2478] and the identical [:2528]) uses the
    textbook predictor
      [p = (pa <= pb && pa <= pc) ? a : (pb <= pc) ? b : c].
    The READ side ([pngrutil.c:4020-4032] and [:4064-4076]) uses an
    optimised running minimum instead:
      [if (pb < pa) { pa = pb; a = b; }   if (pc < pa) a = c;]
    — note [pa] is overwritten, so the second test is against [min pa pb].
    Both are transcribed ([paeth_spec], [paeth_opt]) and
    [paeth_opt_eq_spec] proves them equal; that equality is exactly what
    the round-trip obligation consumes.  A third quirk: the 1-byte-pixel
    reader keeps [a] and [c] in REGISTERS across trips and masks [a] only
    at the top of the next trip ([pngrutil.c:4008]); [rf_paeth1_dec]
    proves that register-carrying loop equal to the uniform body.

    ** Bug-for-bug item: the encoder's early-out leaves [try_row] partial

    Each [png_setup_*_row] breaks as soon as its running sum exceeds
    [lmins] ([pngwutil.c:2309], [:2356], [:2412], [:2489]), leaving the
    rest of [try_row] holding whatever the PREVIOUS candidate wrote.  That
    is safe only because a broken-out sum is [> lmins = mins], so the
    filter cannot then be selected: [setup_complete] is that argument, and
    it is why the heuristic's sums never need a semantic meaning
    (c5-invariants.md §2.2).  Note also that the PAETH arm of
    [png_write_find_filter] ([pngwutil.c:2727-2735]) omits the
    [mins = sum] its three siblings perform — harmless only because PAETH
    is tried last.  Transcribed as written ([ff_step]'s [upd_mins]).

    ** Row 0

    [png_write_start_row] allocates [prev_row] with [png_calloc]
    ([pngwutil.c:1974]) and the reader zero-fills its own, so row 0's
    previous row is all zeros.  A [list Z] shorter than the row (in
    particular [[]]) models that exactly: [nthz] reads 0 past the end
    ([nthz_nil]).  The round-trip theorem is stated for an ARBITRARY
    [prev], so row 0 is the [prev = []] instance.

    Validated against the delivered binary: see
    [a working folder]. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Constants *)

(** [png.h:1475-1480]: the byte stored in the filter position. *)
Definition PF_NONE  : Z := 0.
Definition PF_SUB   : Z := 1.
Definition PF_UP    : Z := 2.
Definition PF_AVG   : Z := 3.
Definition PF_PAETH : Z := 4.
Definition PF_LAST  : Z := 5.

(** [png.h:1463-1470]: the bitmask in [png_ptr->do_filter]. *)
Definition FB_NONE  : Z := 8.
Definition FB_SUB   : Z := 16.
Definition FB_UP    : Z := 32.
Definition FB_AVG   : Z := 64.
Definition FB_PAETH : Z := 128.
Definition FB_ALL   : Z := 248.   (* PNG_ALL_FILTERS *)

(** [size_t] on riscv64. *)
Definition PNG_SIZE_MAX : Z := 18446744073709551615.

(** ** Row access

    A row is a [list Z] of bytes.  Reading before the start of a row, or
    past its end, yields 0 — which is what libpng's separate
    "first [bpp] bytes" loops compute (see [pred_*_first]) and what a
    [png_calloc]ed previous row holds. *)
Definition nthz (l : list Z) (i : Z) : Z :=
  if Z.ltb i 0 then 0 else nth (Z.to_nat i) l 0.

Lemma nthz_neg : forall l i, i < 0 -> nthz l i = 0.
Proof. intros l i H; unfold nthz; now rewrite (proj2 (Z.ltb_lt i 0) H). Qed.

Lemma nthz_nil : forall i, nthz [] i = 0.
Proof. intro i; unfold nthz; destruct (Z.ltb i 0); [reflexivity | now destruct (Z.to_nat i)]. Qed.

Lemma nthz_cons0 : forall v l, nthz (v :: l) 0 = v.
Proof. reflexivity. Qed.

Lemma nthz_nonneg : forall l i, (forall x, In x l -> 0 <= x) -> 0 <= nthz l i.
Proof.
  intros l i H; unfold nthz; destruct (Z.ltb i 0); [lia|].
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [Hlt|Hge].
  - apply H, nth_In, Hlt.
  - rewrite nth_overflow by exact Hge; lia.
Qed.

(** ** The Paeth predictor, in libpng's two formulations *)

(** [pngwutil.c:2464-2478] — the write side, i.e. the textbook PNG
    predictor with ties favouring a, then b. *)
Definition paeth_spec (a b c : Z) : Z :=
  let p  := b - c in
  let q  := a - c in
  let pa := Z.abs p in
  let pb := Z.abs q in
  let pc := Z.abs (p + q) in
  if andb (Z.leb pa pb) (Z.leb pa pc) then a
  else if Z.leb pb pc then b else c.

(** [pngrutil.c:4013-4032] — the read side's running-minimum form. *)
Definition paeth_opt (a b c : Z) : Z :=
  let p   := b - c in
  let q   := a - c in
  let pa  := Z.abs p in
  let pb  := Z.abs q in
  let pc  := Z.abs (p + q) in
  let pa' := if Z.ltb pb pa then pb else pa in   (* if (pb < pa) pa = pb; *)
  let a'  := if Z.ltb pb pa then b  else a  in   (*              a  = b;  *)
  if Z.ltb pc pa' then c else a'.                (* if (pc < pa) a  = c;  *)

Lemma paeth_opt_eq_spec : forall a b c, paeth_opt a b c = paeth_spec a b c.
Proof.
  intros a b c; unfold paeth_opt, paeth_spec.
  set (x := Z.abs (b - c)); set (y := Z.abs (a - c)); set (z := Z.abs (b - c + (a - c))).
  destruct (Z.ltb y x) eqn:E1; destruct (Z.ltb z y) eqn:E2; destruct (Z.ltb z x) eqn:E3;
    destruct (Z.leb x y) eqn:E4; destruct (Z.leb x z) eqn:E5; destruct (Z.leb y z) eqn:E6;
    cbn [andb]; try reflexivity; exfalso;
    repeat match goal with
           | H : Z.ltb _ _ = true  |- _ => apply Z.ltb_lt in H
           | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
           | H : Z.leb _ _ = true  |- _ => apply Z.leb_le in H
           | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
           end; lia.
Qed.

(** ** The five predictors, uniformly

    [pred f a b c] is the value libpng subtracts (encode) or adds (decode)
    at one byte, with [a] the byte [bpp] to the left of the current one,
    [b] the byte above, [c] the byte above-left.  The C's [/2] in AVG is on
    a non-negative sum, so it is [Z]'s [/]. *)
Definition pred (f a b c : Z) : Z :=
  if Z.eqb f PF_NONE then 0
  else if Z.eqb f PF_SUB then a
  else if Z.eqb f PF_UP then b
  else if Z.eqb f PF_AVG then (a + b) / 2
  else paeth_spec a b c.

Lemma pred_none  : forall a b c, pred PF_NONE  a b c = 0. Proof. reflexivity. Qed.
Lemma pred_sub   : forall a b c, pred PF_SUB   a b c = a. Proof. reflexivity. Qed.
Lemma pred_up    : forall a b c, pred PF_UP    a b c = b. Proof. reflexivity. Qed.
Lemma pred_avg   : forall a b c, pred PF_AVG   a b c = (a + b) / 2. Proof. reflexivity. Qed.
Lemma pred_paeth : forall a b c, pred PF_PAETH a b c = paeth_spec a b c. Proof. reflexivity. Qed.

(** libpng runs the first [bpp] bytes of SUB / AVG / PAETH through separate
    loops ([pngrutil.c:3944] vs [:3956], [:3971] vs [:3980], [:4046] vs
    [:4059]; [pngwutil.c:2288] vs [:2298], [:2392] vs [:2402], [:2455] vs
    [:2465]).  Those loops are the general body with [a = c = 0]; only the
    Paeth instance is non-obvious. *)
Lemma pred_sub_first : forall b, pred PF_SUB 0 b 0 = 0.
Proof. reflexivity. Qed.

Lemma pred_avg_first : forall b, pred PF_AVG 0 b 0 = b / 2.
Proof. intro b; change (pred PF_AVG 0 b 0) with ((0 + b) / 2); f_equal; lia. Qed.

Lemma pred_paeth_first : forall b, 0 <= b -> pred PF_PAETH 0 b 0 = b.
Proof.
  intros b Hb; change (pred PF_PAETH 0 b 0) with (paeth_spec 0 b 0).
  unfold paeth_spec.
  rewrite !Z.sub_0_r, Z.abs_0, Z.add_0_r, (Z.abs_eq b) by exact Hb.
  destruct (Z.eq_dec b 0) as [->|Hne]; [reflexivity|].
  replace (Z.leb b 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb 0 b) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

(** ** Encode and decode

    [pre] is the reversed prefix of the ORIGINAL row (encode reads its left
    neighbour from the unfiltered row, [pngwutil.c:2302] [*lp]); [out] is
    the reversed prefix of the DECODED row (decode reads its left
    neighbour from the already-unfiltered output, [pngrutil.c:3943]
    [*(rp-bpp)]).  [nthz _ (bpp - 1)] on a reversed prefix is exactly
    [x[i - bpp]], and it is 0 while fewer than [bpp] bytes exist — which is
    libpng's first loop. *)
Fixpoint enc_go (f bpp : Z) (prev : list Z) (i : Z) (pre : list Z)
                (l : list Z) {struct l} : list Z :=
  match l with
  | [] => []
  | x :: r =>
      u8 (x - pred f (nthz pre (bpp - 1)) (nthz prev i) (nthz prev (i - bpp)))
      :: enc_go f bpp prev (i + 1) (x :: pre) r
  end.

Fixpoint dec_go (f bpp : Z) (prev : list Z) (i : Z) (out : list Z)
                (l : list Z) {struct l} : list Z :=
  match l with
  | [] => []
  | y :: r =>
      let v := u8 (y + pred f (nthz out (bpp - 1)) (nthz prev i) (nthz prev (i - bpp))) in
      v :: dec_go f bpp prev (i + 1) (v :: out) r
  end.

(** The encoder's [png_setup_*_row_only] and the decoder's
    [pp->read_filter[filter-1]], as functions of whole rows. *)
Definition filter_model (f bpp : Z) (prev row : list Z) : list Z :=
  enc_go f bpp prev 0 [] row.

Definition unfilter_model (f bpp : Z) (prev row : list Z) : list Z :=
  dec_go f bpp prev 0 [] row.

(** [pngrutil.c:4130-4145] [png_read_filter_row]: filter bytes outside
    [1 .. PNG_FILTER_VALUE_LAST-1] leave the row untouched. *)
Definition png_read_filter_row (bpp filter : Z) (prev row : list Z) : list Z :=
  if andb (Z.ltb PF_NONE filter) (Z.ltb filter PF_LAST)
  then unfilter_model filter bpp prev row
  else row.

(** The named decoder entry points, for citation. *)
Definition png_read_filter_row_sub (bpp : Z) (row : list Z) : list Z :=
  dec_go PF_SUB bpp [] 0 [] row.
(** [bpp] is unused by the UP predictor — the C function has no such
    parameter ([pngrutil.c:3949]) — but is kept so that every entry point
    has the same shape. *)
Definition png_read_filter_row_up (bpp : Z) (prev row : list Z) : list Z :=
  dec_go PF_UP bpp prev 0 [] row.
Definition png_read_filter_row_avg (bpp : Z) (prev row : list Z) : list Z :=
  dec_go PF_AVG bpp prev 0 [] row.
Definition png_read_filter_row_paeth_multibyte_pixel (bpp : Z) (prev row : list Z) : list Z :=
  dec_go PF_PAETH bpp prev 0 [] row.

(** BUG-FOR-BUG: the 1-byte-pixel Paeth reader NEVER reads
    [row_info->pixel_depth] ([pngrutil.c:3990-4038] has no [bpp] local at
    all) — it hard-codes a one-byte pixel.  It is correct only because
    [png_init_filter_functions] ([pngrutil.c:4110-4116]) installs it solely
    when [bpp == 1].  Called with a wider pixel it silently unfilters as if
    [bpp = 1]; the differential harness reproduces exactly that (its
    injected [bpp2-rb2-*] cases), so the model must NOT take a [bpp]. *)
Definition png_read_filter_row_paeth_1byte_pixel (prev row : list Z) : list Z :=
  dec_go PF_PAETH 1 prev 0 [] row.

(** ** [png_read_filter_row_paeth_1byte_pixel] ([pngrutil.c:3990-4038])

    Transcribed with its two register carries: [a] holds the PREVIOUS
    output byte UNMASKED (it is masked at [:4008], at the top of the next
    trip) and [c] holds the previous [prev_row] byte ([:4033] [c = b]). *)
Fixpoint rf_p1_go (a c : Z) (prev : list Z) (i : Z) (l : list Z) {struct l} : list Z :=
  match l with
  | [] => []
  | y :: r =>
      let a0 := Z.land a 255 in            (* :4008 [a &= 0xff] *)
      let b  := nthz prev i in             (* :4009 [b = *prev_row++] *)
      let w  := paeth_opt a0 b c in        (* :4011-4032 *)
      let a' := w + y in                   (* :4036 [a += *row] *)
      u8 a' :: rf_p1_go a' b prev (i + 1) r
  end.

(** :3995-3999, the first pixel: [c = *prev_row++; a = *row + c;]. *)
Definition rf_paeth1 (prev row : list Z) : list Z :=
  match row with
  | [] => []
  | y :: r => let c := nthz prev 0 in
              let a := y + c in
              u8 a :: rf_p1_go a c prev 1 r
  end.

(** ** Elementary facts *)

Lemma land255_u8 : forall a, 0 <= a -> Z.land a 255 = u8 a.
Proof.
  intros a Ha; unfold u8.
  replace 255 with (Z.ones 8) by reflexivity.
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma u8_bounds : forall a, 0 <= u8 a < 256.
Proof. intro a; unfold u8; apply Z.mod_pos_bound; lia. Qed.

Lemma paeth_spec_nonneg :
  forall a b c, 0 <= a -> 0 <= b -> 0 <= c -> 0 <= paeth_spec a b c.
Proof.
  intros a b c Ha Hb Hc; unfold paeth_spec.
  destruct (andb _ _); [exact Ha|]. destruct (Z.leb _ _); [exact Hb|exact Hc].
Qed.

(** [dec_go] undoes [enc_go]: the two threads carry the SAME accumulator,
    so the predictors coincide byte by byte and the [u8]s cancel. *)
Lemma dec_enc_go :
  forall l f bpp prev i pre,
    Forall (fun x => 0 <= x < 256) l ->
    dec_go f bpp prev i pre (enc_go f bpp prev i pre l) = l.
Proof.
  induction l as [|x r IH]; intros f bpp prev i pre HF; [reflexivity|].
  inversion HF as [|x' r' Hx HR]; subst.
  cbn [enc_go dec_go].
  set (P := pred f (nthz pre (bpp - 1)) (nthz prev i) (nthz prev (i - bpp))).
  replace (u8 (u8 (x - P) + P)) with x.
  2:{ unfold u8. rewrite Zplus_mod_idemp_l.
      replace (x - P + P) with x by lia. symmetry; apply Z.mod_small; lia. }
  f_equal. now apply IH.
Qed.

(** The direct obligation of the round-trip DAG, for every filter type and
    every previous row (row 0 is the [prev = []] instance). *)
Theorem unfilter_filter_id :
  forall f bpp prev row,
    Forall (fun x => 0 <= x < 256) row ->
    unfilter_model f bpp prev (filter_model f bpp prev row) = row.
Proof. intros; unfold unfilter_model, filter_model; now apply dec_enc_go. Qed.

Corollary unfilter_filter_id_row0 :
  forall f bpp row,
    Forall (fun x => 0 <= x < 256) row ->
    unfilter_model f bpp [] (filter_model f bpp [] row) = row.
Proof. intros; now apply unfilter_filter_id. Qed.

(** Filter NONE is the identity on a byte row, so [png_write_find_filter]'s
    [best_row = row_buf] default really is [filter_model PF_NONE]. *)
Lemma enc_go_none :
  forall l bpp prev i pre, Forall (fun x => 0 <= x < 256) l ->
    enc_go PF_NONE bpp prev i pre l = l.
Proof.
  induction l as [|x r IH]; intros bpp prev i pre HF; [reflexivity|].
  inversion HF as [|x' r' Hx HR]; subst. cbn [enc_go].
  change (pred PF_NONE (nthz pre (bpp - 1)) (nthz prev i) (nthz prev (i - bpp)))
    with 0.
  rewrite Z.sub_0_r, u8_id by lia.
  f_equal. now apply IH.
Qed.

Lemma filter_model_none :
  forall bpp prev row, Forall (fun x => 0 <= x < 256) row ->
    filter_model PF_NONE bpp prev row = row.
Proof. intros; unfold filter_model; now apply enc_go_none. Qed.

(** The 1-byte Paeth reader's register carries are the uniform body's
    accumulators. *)
Lemma rf_p1_go_dec :
  forall l a c prev i out,
    (forall x, In x prev -> 0 <= x) ->
    (forall x, In x l -> 0 <= x) ->
    0 <= a ->
    Z.land a 255 = nthz out 0 ->
    c = nthz prev (i - 1) ->
    rf_p1_go a c prev i l = dec_go PF_PAETH 1 prev i out l.
Proof.
  induction l as [|y r IH]; intros a c prev i out Hp Hl Ha Hout Hc; [reflexivity|].
  assert (Hy : 0 <= y) by (apply Hl; now left).
  assert (Hb : 0 <= nthz prev i) by (apply nthz_nonneg; exact Hp).
  assert (Hc0 : 0 <= c) by (subst c; apply nthz_nonneg; exact Hp).
  assert (Ha0 : 0 <= Z.land a 255) by (apply Z.land_nonneg; now left).
  assert (Hw : 0 <= paeth_spec (nthz out 0) (nthz prev i) c)
    by (apply paeth_spec_nonneg; [rewrite <- Hout; exact Ha0 | exact Hb | exact Hc0]).
  cbn [rf_p1_go dec_go].
  rewrite paeth_opt_eq_spec, Hout.
  replace (pred PF_PAETH (nthz out (1 - 1)) (nthz prev i) (nthz prev (i - 1)))
     with (paeth_spec (nthz out 0) (nthz prev i) c)
     by (rewrite Hc; replace (1 - 1) with 0 by lia; reflexivity).
  rewrite (Z.add_comm y (paeth_spec (nthz out 0) (nthz prev i) c)). f_equal.
  apply IH.
  - exact Hp.
  - intros x Hx; apply Hl; now right.
  - lia.
  - rewrite nthz_cons0. apply land255_u8; lia.
  - replace (i + 1 - 1) with i by lia. reflexivity.
Qed.

Theorem rf_paeth1_dec :
  forall prev row,
    (forall x, In x prev -> 0 <= x) ->
    (forall x, In x row -> 0 <= x) ->
    rf_paeth1 prev row = dec_go PF_PAETH 1 prev 0 [] row.
Proof.
  intros prev row Hp Hr. destruct row as [|y r]; [reflexivity|].
  assert (Hy : 0 <= y) by (apply Hr; now left).
  assert (Hc : 0 <= nthz prev 0) by (apply nthz_nonneg; exact Hp).
  cbn [rf_paeth1 dec_go].
  replace (pred PF_PAETH (nthz [] (1 - 1)) (nthz prev 0) (nthz prev (0 - 1)))
     with (nthz prev 0)
     by (rewrite nthz_nil, (nthz_neg prev (0 - 1)) by lia;
         symmetry; apply pred_paeth_first; exact Hc).
  rewrite (Z.add_comm y (nthz prev 0)). f_equal.
  apply rf_p1_go_dec.
  - exact Hp.
  - intros x Hx; apply Hr; now right.
  - lia.
  - rewrite nthz_cons0. apply land255_u8; lia.
  - replace (1 - 1) with 0 by lia. reflexivity.
Qed.

(** ** The encoder's heuristic ([pngwutil.c:2278-2734])

    Everything below is QUARANTINED: the only facts the correctness core
    consumes are [find_filter_contract]'s two conjuncts.  The sums are
    transcribed exactly (they decide which filter is emitted, so refinement
    needs them) but are never given a semantic meaning. *)

(** [pngwutil.c:2297] (the non-[PNG_USE_ABS] arm):
    [sum += (v < 128) ? v : 256 - v]. *)
Definition msd (v : Z) : Z := if Z.ltb v 128 then v else 256 - v.

(** [pngwutil.c:2617-2627]: the 'none' candidate's sum. *)
Definition find_none_sum (row : list Z) : Z :=
  fold_left (fun s x => s + msd x) row 0.

(** One [png_setup_*_row].  [nb] is the number of leading bytes whose loop
    carries NO early-out test: [bpp] for SUB / AVG / PAETH (their first
    loops, [pngwutil.c:2288-2296], [:2392-2400], [:2455-2463], have none)
    and 0 for UP, which is a single loop tested from [i = 0]
    ([:2345-2358]).  On break, the byte just written IS in [try_row]; the
    rest keeps whatever the previous candidate left there, which is why
    the second component is a PREFIX. *)
Fixpoint setup_go (f bpp lmins : Z) (prev : list Z) (i : Z) (pre : list Z)
                  (nb sum : Z) (l : list Z) {struct l} : Z * list Z :=
  match l with
  | [] => (sum, [])
  | x :: r =>
      let v := u8 (x - pred f (nthz pre (bpp - 1)) (nthz prev i) (nthz prev (i - bpp))) in
      let s := sum + msd v in
      if andb (Z.leb nb i) (Z.ltb lmins s)
      then (s, [v])                                (* break *)
      else let '(s', o) := setup_go f bpp lmins prev (i + 1) (x :: pre) nb s r in
           (s', v :: o)
  end.

Definition png_setup_sub_row (bpp lmins : Z) (prev row : list Z) : Z * list Z :=
  setup_go PF_SUB bpp lmins prev 0 [] bpp 0 row.
(** [bpp] is unused by the UP predictor (the C signature omits it,
    [pngwutil.c:2338]); it is threaded only to keep the shape uniform. *)
Definition png_setup_up_row (bpp lmins : Z) (prev row : list Z) : Z * list Z :=
  setup_go PF_UP bpp lmins prev 0 [] 0 0 row.
Definition png_setup_avg_row (bpp lmins : Z) (prev row : list Z) : Z * list Z :=
  setup_go PF_AVG bpp lmins prev 0 [] bpp 0 row.
Definition png_setup_paeth_row (bpp lmins : Z) (prev row : list Z) : Z * list Z :=
  setup_go PF_PAETH bpp lmins prev 0 [] bpp 0 row.

(** The [_only] variants ([pngwutil.c:2316-2336], [:2361-2371],
    [:2422-2437], [:2505-2536]) are the same loops with the sum and the
    break deleted, i.e. exactly [filter_model]. *)

(** A candidate that is SELECTED never broke out early, so what it left in
    [try_row] is the whole filtered row.  This is the entire contract the
    heuristic owes. *)
Lemma setup_complete :
  forall l f bpp lmins prev i pre nb sum s o,
    setup_go f bpp lmins prev i pre nb sum l = (s, o) ->
    s <= lmins ->
    o = enc_go f bpp prev i pre l.
Proof.
  induction l as [|x r IH]; intros f bpp lmins prev i pre nb sum s o Heq Hs.
  - cbn in Heq; now inversion Heq.
  - cbn [setup_go] in Heq; cbn [enc_go].
    set (v := u8 (x - pred f (nthz pre (bpp - 1)) (nthz prev i) (nthz prev (i - bpp)))) in *.
    destruct (andb (Z.leb nb i) (Z.ltb lmins (sum + msd v))) eqn:Ebr.
    + exfalso. apply andb_prop in Ebr as [_ Eb2]. apply Z.ltb_lt in Eb2.
      injection Heq as Hse _. lia.
    + destruct (setup_go f bpp lmins prev (i + 1) (x :: pre) nb (sum + msd v) r)
        as [s' o'] eqn:Erec.
      injection Heq as Hse Hoe. subst o s'. f_equal.
      eapply IH; [exact Erec | exact Hs].
Qed.

(** ** [png_write_find_filter] ([pngwutil.c:2548-2734])

    State threaded through the four arms: [(mins, (best_filter, best_row))].
    [upd_mins] is [false] only for PAETH, transcribing the missing
    [mins = sum] at [:2729]. *)
Definition ff_step (f bit : Z) (only : list Z) (setup : Z -> Z * list Z)
                   (ftd : Z) (upd_mins : bool)
                   (st : Z * (Z * list Z)) : Z * (Z * list Z) :=
  let mins := fst st in
  if Z.eqb ftd bit then (mins, (f, only))          (* the only filter: no test *)
  else if negb (Z.eqb (Z.land ftd bit) 0) then
    let '(s, o) := setup mins in
    if Z.ltb s mins then ((if upd_mins then s else mins), (f, o)) else st
  else st.

(** The four arms, with [ftd] and the initial [mins] abstracted so that the
    contract can be proved once, independently of the guard computation. *)
Definition ff_pick (ftd mins0 bpp : Z) (prev row : list Z) : Z * (Z * list Z) :=
  ff_step PF_PAETH FB_PAETH (filter_model PF_PAETH bpp prev row)
          (fun m => png_setup_paeth_row bpp m prev row) ftd false
 (ff_step PF_AVG FB_AVG (filter_model PF_AVG bpp prev row)
          (fun m => png_setup_avg_row bpp m prev row) ftd true
 (ff_step PF_UP FB_UP (filter_model PF_UP bpp prev row)
          (fun m => png_setup_up_row bpp m prev row) ftd true
 (ff_step PF_SUB FB_SUB (filter_model PF_SUB bpp prev row)
          (fun m => png_setup_sub_row bpp m prev row) ftd true
          (mins0, (PF_NONE, row))))).

(** [smax] is [PNG_SIZE_MAX], i.e. the target's [(size_t)-1].  It is a
    parameter only so that the differential harness can extract this model
    to OCaml, whose native [int] is 63 bits and cannot hold [2^64 - 1]; the
    contract below is proved for EVERY [smax], and
    [png_write_find_filter] instantiates it at the riscv64 value. *)
Definition png_write_find_filter_at (smax do_filter bpp : Z) (prev row : list Z)
  : Z * list Z :=
  let row_bytes := Z.of_nat (length row) in
  (* :2600-2604 overflow guard: keep only the lowest set filter bit *)
  let ovf  := Z.leb (smax / 128) row_bytes in
  let ftd  := if ovf then Z.land do_filter (- do_filter) else do_filter in
  (* :2570 [mins = PNG_SIZE_MAX - 256]; :2608-2630 the 'none' sum *)
  let mins0 :=
    if ovf then smax - 256
    else if andb (negb (Z.eqb (Z.land ftd FB_NONE) 0)) (negb (Z.eqb ftd FB_NONE))
         then find_none_sum row
         else smax - 256 in
  snd (ff_pick ftd mins0 bpp prev row).

Definition png_write_find_filter (do_filter bpp : Z) (prev row : list Z)
  : Z * list Z :=
  png_write_find_filter_at PNG_SIZE_MAX do_filter bpp prev row.

(** The contract, and the ONLY thing the correctness core is allowed to
    know about the heuristic. *)
Definition ff_inv (bpp : Z) (prev row : list Z) (st : Z * (Z * list Z)) : Prop :=
  0 <= fst (snd st) <= 4 /\ snd (snd st) = filter_model (fst (snd st)) bpp prev row.

Lemma ff_step_inv :
  forall bpp prev row f bit only setup ftd um st,
    0 <= f <= 4 ->
    only = filter_model f bpp prev row ->
    (forall m s o, setup m = (s, o) -> s <= m -> o = filter_model f bpp prev row) ->
    ff_inv bpp prev row st ->
    ff_inv bpp prev row (ff_step f bit only setup ftd um st).
Proof.
  intros bpp prev row f bit only setup ftd um st Hf Honly Hsetup Hinv.
  unfold ff_step. destruct (Z.eqb ftd bit).
  - split; cbn; [exact Hf | exact Honly].
  - destruct (negb (Z.eqb (Z.land ftd bit) 0)); [|exact Hinv].
    destruct (setup (fst st)) as [s o] eqn:Es.
    destruct (Z.ltb_spec s (fst st)) as [Hlt|Hge]; [|exact Hinv].
    split; cbn; [exact Hf | eapply Hsetup; [exact Es | lia]].
Qed.

Lemma ff_pick_inv :
  forall ftd mins0 bpp prev row,
    Forall (fun x => 0 <= x < 256) row ->
    ff_inv bpp prev row (ff_pick ftd mins0 bpp prev row).
Proof.
  intros ftd mins0 bpp prev row Hrow. unfold ff_pick.
  repeat (apply ff_step_inv;
          [ unfold PF_SUB, PF_UP, PF_AVG, PF_PAETH; lia
          | reflexivity
          | intros m s o Hgo Hs;
            unfold png_setup_sub_row, png_setup_up_row, png_setup_avg_row,
                   png_setup_paeth_row, filter_model in *;
            eapply setup_complete; [exact Hgo | exact Hs]
          | ]).
  split; cbn.
  - unfold PF_NONE; lia.
  - symmetry; now apply filter_model_none.
Qed.

Lemma ff_pick_contract :
  forall ftd mins0 bpp prev row,
    Forall (fun x => 0 <= x < 256) row ->
    let '(f, o) := snd (ff_pick ftd mins0 bpp prev row) in
    0 <= f <= 4 /\ o = filter_model f bpp prev row.
Proof.
  intros ftd mins0 bpp prev row Hrow.
  pose proof (ff_pick_inv ftd mins0 bpp prev row Hrow) as H.
  unfold ff_inv in H. revert H.
  destruct (snd (ff_pick ftd mins0 bpp prev row)) as [f o].
  cbn. exact (fun h => h).
Qed.

Theorem find_filter_at_contract :
  forall smax do_filter bpp prev row,
    Forall (fun x => 0 <= x < 256) row ->
    let '(f, o) := png_write_find_filter_at smax do_filter bpp prev row in
    0 <= f <= 4 /\ o = filter_model f bpp prev row.
Proof.
  intros smax do_filter bpp prev row Hrow.
  unfold png_write_find_filter_at; cbv zeta.
  apply ff_pick_contract; exact Hrow.
Qed.

Theorem find_filter_contract :
  forall do_filter bpp prev row,
    Forall (fun x => 0 <= x < 256) row ->
    let '(f, o) := png_write_find_filter do_filter bpp prev row in
    0 <= f <= 4 /\ o = filter_model f bpp prev row.
Proof.
  intros do_filter bpp prev row Hrow.
  unfold png_write_find_filter. now apply find_filter_at_contract.
Qed.

(** ** The encoder's filter set on this driver's path

    [png_write_IHDR] ([pngwutil.c:824-831]): if the application never
    called [png_set_filter] — and [harness/src/png_harness.c] never does —
    [do_filter] is [PNG_NO_FILTERS] at IHDR time and becomes
    [PNG_FILTER_NONE] (0x08) for palette or sub-byte images and
    [PNG_ALL_FILTERS] (0xf8) otherwise.  [encode_raw] only ever writes
    GRAY / RGB / RGBA / GRAY_ALPHA at bit depth 8 or 16, so the default on
    the round-trip path is ALWAYS [PNG_ALL_FILTERS]. *)
Definition png_ihdr_do_filter (color_type bit_depth : Z) : Z :=
  if orb (Z.eqb color_type 3) (Z.ltb bit_depth 8) then FB_NONE else FB_ALL.

(** [png_write_start_row] ([pngwutil.c:1931-1941]) then narrows the set by
    image shape: [h = 1] clears UP|AVG|PAETH (mask 0x1f), [w = 1] clears
    SUB|AVG|PAETH (mask 0x2f), and an empty set becomes NONE.  With
    [w, h in 1..64] (the harness's range) all four outcomes occur: 0xf8,
    0x18 ([h = 1]), 0x28 ([w = 1]) and 0x08 ([w = h = 1]).  [tst_row] is
    allocated only when more than one of SUB/UP/AVG/PAETH survives
    ([:1960-1962]), which is exactly why the "no swap, so the next
    candidate overwrites the current best" hazard is unreachable: with one
    candidate there is no next one. *)
Definition png_start_row_filters (do_filter width height : Z) : Z :=
  let f1 := if Z.eqb height 1 then Z.land do_filter 31 else do_filter in
  let f2 := if Z.eqb width 1 then Z.land f1 47 else f1 in
  if Z.eqb f2 0 then FB_NONE else f2.
