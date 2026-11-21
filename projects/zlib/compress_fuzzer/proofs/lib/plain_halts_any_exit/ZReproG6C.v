(** * ZReproG6C — G6 bound-fit, part C: [compress_block]'s exact bit cost.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-19).

    The LENGTH analogue of CbFold's [compress_block_emits]: the fold over
    the symbol buffer appends exactly [toks_cost] bits plus the END_BLOCK
    code, where [toks_cost] is the per-token sum of code length + extra
    bits.  Then the REGROUP: the per-token sum equals the per-symbol
    frequency-weighted sum in the [count_L]/[count_D] vocabulary — the
    seam [FreqInv] converts to tree frequencies, which is what ties
    emitted bits to zlib's [opt_len]/[static_len] counters in part E.

    Only length facts are used: no code-range, Kraft, or decodability
    premise appears — [LenB] (all code lengths in [0,15]) is the whole
    tree-side obligation (see ZReproG6A's header).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees CbEmit CbFold BtWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 ZReproG6A
  SwTally.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Extra-bits table ranges (reflection, CbEmit's forallb tooling).
   ========================================================================== *)

Definition g6_elb_at (c : Z) : bool :=
  (0 <=? extra_lbits c) && (extra_lbits c <=? 16).

Lemma g6_elb_all : forallb g6_elb_at (zseq 29 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma extra_lbits_range : forall c, 0 <= c < 29 -> 0 <= extra_lbits c <= 16.
Proof.
  intros c Hc.
  pose proof (forallb_zseq' g6_elb_at 29 29 c
                ltac:(vm_compute; reflexivity) g6_elb_all Hc) as H.
  unfold g6_elb_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Definition g6_edb_at (c : Z) : bool :=
  (0 <=? extra_dbits c) && (extra_dbits c <=? 16).

Lemma g6_edb_all : forallb g6_edb_at (zseq 30 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma extra_dbits_range : forall c, 0 <= c < 30 -> 0 <= extra_dbits c <= 16.
Proof.
  intros c Hc.
  pose proof (forallb_zseq' g6_edb_at 30 30 c
                ltac:(vm_compute; reflexivity) g6_edb_all Hc) as H.
  unfold g6_edb_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ==========================================================================
   2.  The cost vocabulary.
   ========================================================================== *)

(** Per-token emitted bits, exactly as [cb_step] sends them. *)
Definition tok_cost (lt dt : Tree) (t : Tok) : Z :=
  match t with
  | TLit b => t_len lt b
  | TMatch len dist =>
      let code := length_code (len - 3) in
      let dc := d_code (dist - 1) in
      t_len lt (code + LITERALS + 1) + extra_lbits code
      + t_len dt dc + extra_dbits dc
  end.

Fixpoint toks_cost (lt dt : Tree) (ts : list Tok) : Z :=
  match ts with
  | [] => 0
  | t :: r => tok_cost lt dt t + toks_cost lt dt r
  end.

(** Per-symbol cost — [olterm]/[slterm]'s [t_len + xbits] at the emitter's
    index conventions ([sd_extra_base TK_L = LITERALS + 1],
    [sd_extra_base TK_D = 0]). *)
Definition cost_L (lt : Tree) (i : Z) : Z :=
  t_len lt i
  + (if Z.leb (LITERALS + 1) i then extra_lbits (i - (LITERALS + 1)) else 0).

Definition cost_D (dt : Tree) (i : Z) : Z := t_len dt i + extra_dbits i.

(** All code lengths of the first [n] entries within the writer window. *)
Definition LenB (t : Tree) (n : Z) : Prop :=
  forall i, 0 <= i < n -> 0 <= t_len t i <= 15.

Lemma tok_cost_nonneg : forall lt dt t,
  LenB lt 286 -> LenB dt 30 -> tok_enc t -> 0 <= tok_cost lt dt t.
Proof.
  intros lt dt t HL HD He.
  destruct t as [b | len dist]; cbn [tok_cost] in *.
  - destruct He as [Hb0 Hb1].
    pose proof (HL b ltac:(unfold LITERALS in *; lia)). lia.
  - destruct He as [[Hl0 Hl1] [Hd0 Hd1]].
    unfold MIN_MATCH in Hl0. unfold MAX_MATCH in Hl1. cbv zeta.
    destruct (lcode_range (len - 3) ltac:(lia)) as [Hc _].
    destruct (DcodeRange_all (dist - 1) ltac:(lia)) as [Hdc _].
    pose proof (extra_lbits_range (length_code (len - 3)) Hc).
    pose proof (extra_dbits_range (d_code (dist - 1)) Hdc).
    pose proof (HL (length_code (len - 3) + LITERALS + 1)
                  ltac:(unfold LITERALS in *; lia)).
    pose proof (HD (d_code (dist - 1)) ltac:(lia)).
    lia.
Qed.

Lemma toks_cost_nonneg : forall lt dt ts,
  LenB lt 286 -> LenB dt 30 -> cEnc ts -> 0 <= toks_cost lt dt ts.
Proof.
  intros lt dt ts HL HD He.
  induction ts as [|t r IH]; cbn [toks_cost]; [lia|].
  inversion He as [|? ? Ht Hr]; subst.
  pose proof (tok_cost_nonneg lt dt t HL HD Ht).
  pose proof (IH Hr). lia.
Qed.

(* ==========================================================================
   3.  One [cb_step].
   ========================================================================== *)

Lemma cb_step_len : forall sym symnext lt dt st,
  bwv (c_bw st) ->
  tok_enc (tok_at sym (c_sx st)) ->
  LenB lt 286 -> LenB dt 30 ->
  zbits (c_bw (cb_out (cb_step sym symnext lt dt st)))
    = zbits (c_bw st) + tok_cost lt dt (tok_at sym (c_sx st))
  /\ bwv (c_bw (cb_out (cb_step sym symnext lt dt st))).
Proof.
  intros sym symnext lt dt st Hb He HL HD.
  unfold tok_at, cb_dist, cb_lc in He |- *.
  unfold cb_step, cb_out. cbv zeta.
  set (dist := Z.land (sym (c_sx st)) 255
               + Z.shiftl (Z.land (sym (c_sx st + 1)) 255) 8) in *.
  set (lc := sym (c_sx st + 2)) in *.
  destruct (Z.eqb_spec dist 0) as [E|E].
  - (* literal *)
    assert (He' : 0 <= lc < 256) by exact He.
    cbn [tok_cost].
    destruct (zbits_send_code lc lt (c_bw st) Hb
                ltac:(unfold Buf_size;
                      pose proof (HL lc ltac:(unfold LITERALS in *; lia));
                      lia)) as [Hz Hv].
    destruct (Z.ltb (c_sx st + 3) symnext); cbn [c_bw c_sx];
      split; assumption.
  - (* match *)
    assert (He' : MIN_MATCH <= lc + 3 <= MAX_MATCH /\ 1 <= dist <= 32768)
      by exact He.
    destruct He' as [[Hl0 Hl1] [Hd0 Hd1]].
    unfold MIN_MATCH in Hl0. unfold MAX_MATCH in Hl1.
    cbn [tok_cost]. cbv zeta.
    replace (lc + 3 - 3) with lc by ring.
    destruct (lcode_range lc ltac:(lia)) as [Hc _].
    destruct (DcodeRange_all (dist - 1) ltac:(lia)) as [Hdc _].
    pose proof (extra_lbits_range (length_code lc) Hc) as Hel.
    pose proof (extra_dbits_range (d_code (dist - 1)) Hdc) as Hed.
    (* the four sends, threaded *)
    destruct (zbits_send_code (length_code lc + LITERALS + 1) lt (c_bw st) Hb
                ltac:(unfold Buf_size;
                      pose proof (HL (length_code lc + LITERALS + 1)
                                    ltac:(unfold LITERALS in *; lia));
                      lia)) as [Z1 V1].
    set (b1 := send_code (length_code lc + LITERALS + 1) lt (c_bw st)) in *.
    assert (S2 : zbits (if Z.eqb (extra_lbits (length_code lc)) 0 then b1
                        else bw_send_bits (lc - base_length (length_code lc))
                               (extra_lbits (length_code lc)) b1)
                 = zbits b1 + extra_lbits (length_code lc)
             /\ bwv (if Z.eqb (extra_lbits (length_code lc)) 0 then b1
                     else bw_send_bits (lc - base_length (length_code lc))
                            (extra_lbits (length_code lc)) b1)).
    { destruct (Z.eqb_spec (extra_lbits (length_code lc)) 0) as [E2|E2].
      - rewrite E2. split; [lia | exact V1].
      - apply zbits_send_bits; [exact V1 | unfold Buf_size; lia]. }
    destruct S2 as [Z2 V2].
    set (b2 := if Z.eqb (extra_lbits (length_code lc)) 0 then b1
               else bw_send_bits (lc - base_length (length_code lc))
                      (extra_lbits (length_code lc)) b1) in *.
    destruct (zbits_send_code (d_code (dist - 1)) dt b2 V2
                ltac:(unfold Buf_size;
                      pose proof (HD (d_code (dist - 1)) ltac:(lia));
                      lia)) as [Z3 V3].
    set (b3 := send_code (d_code (dist - 1)) dt b2) in *.
    assert (S4 : zbits (if Z.eqb (extra_dbits (d_code (dist - 1))) 0 then b3
                        else bw_send_bits (dist - 1 - base_dist (d_code (dist - 1)))
                               (extra_dbits (d_code (dist - 1))) b3)
                 = zbits b3 + extra_dbits (d_code (dist - 1))
             /\ bwv (if Z.eqb (extra_dbits (d_code (dist - 1))) 0 then b3
                     else bw_send_bits (dist - 1 - base_dist (d_code (dist - 1)))
                            (extra_dbits (d_code (dist - 1))) b3)).
    { destruct (Z.eqb_spec (extra_dbits (d_code (dist - 1))) 0) as [E4|E4].
      - rewrite E4. split; [lia | exact V3].
      - apply zbits_send_bits; [exact V3 | unfold Buf_size; lia]. }
    destruct S4 as [Z4 V4].
    destruct (Z.ltb (c_sx st + 3) symnext); cbn [c_bw c_sx];
      (split; [rewrite Z4, Z3, Z2, Z1; ring | exact V4]).
Qed.

(* ==========================================================================
   4.  The fold and [compress_block].
   ========================================================================== *)

Lemma cb_loop_len : forall toks t sym symnext lt dt st0,
  bwv (c_bw st0) ->
  BufToks sym (c_sx st0) symnext (t :: toks) ->
  cEnc (t :: toks) ->
  LenB lt 286 -> LenB dt 30 ->
  exists st',
    cb_loop (S (length toks)) sym symnext lt dt st0 = Some st'
    /\ zbits (c_bw st') = zbits (c_bw st0) + toks_cost lt dt (t :: toks)
    /\ bwv (c_bw st').
Proof.
  induction toks as [|t2 toks IH]; intros t sym symnext lt dt st0 Hb Hbuf He HL HD;
    inversion He as [|? ? Ht Hr]; subst;
    pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext;
    destruct (buftoks_cons_inv _ _ _ _ _ Hbuf) as [-> Htail].
  - (* last symbol: the CbDone trip *)
    cbn [length] in Hext.
    destruct (cb_step_len sym symnext lt dt st0 Hb Ht HL HD) as [Hz Hv].
    exists (cb_out (cb_step sym symnext lt dt st0)).
    split; [apply cb_loop_one; lia|].
    split; [|exact Hv].
    rewrite Hz. cbn [toks_cost]. ring.
  - (* interior symbol: CbCont, then the induction *)
    cbn [length] in Hext.
    destruct (cb_step_len sym symnext lt dt st0 Hb Ht HL HD) as [Hz Hv].
    assert (Hlt3 : c_sx st0 + 3 < symnext)
      by (cbn [length] in Hext; lia).
    destruct (IH t2 sym symnext lt dt
                 (cb_out (cb_step sym symnext lt dt st0)) Hv
                 ltac:(rewrite cb_step_sx; exact Htail) Hr HL HD)
      as [st' [Hloop [Hz' Hv']]].
    exists st'.
    split.
    { cbn [length].
      rewrite (cb_loop_step_cont _ sym symnext lt dt st0 Hlt3).
      exact Hloop. }
    split; [|exact Hv'].
    rewrite Hz', Hz. cbn [toks_cost]. ring.
Qed.

Theorem compress_block_len : forall sym symnext lt dt b toks,
  bwv b ->
  BufToks sym 0 symnext toks ->
  cEnc toks ->
  LenB lt 286 -> LenB dt 30 ->
  zbits (compress_block sym symnext lt dt b)
    = zbits b + toks_cost lt dt toks + t_len lt END_BLOCK
  /\ bwv (compress_block sym symnext lt dt b).
Proof.
  intros sym symnext lt dt b toks Hb Hbuf He HL HD.
  assert (Heob : 0 <= t_len lt END_BLOCK <= Buf_size)
    by (unfold Buf_size, END_BLOCK;
        pose proof (HL 256 ltac:(lia)); lia).
  pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext.
  unfold compress_block. cbv zeta.
  destruct toks as [|t toks].
  - cbn [length] in Hext.
    replace (Z.eqb symnext 0) with true
      by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota.
    destruct (zbits_send_code END_BLOCK lt b Hb Heob) as [Hz Hv].
    split; [rewrite Hz; cbn [toks_cost]; ring | exact Hv].
  - cbn [length] in Hext.
    replace (Z.eqb symnext 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    cbv beta iota.
    destruct (cb_loop_len toks t sym symnext lt dt
                {| c_sx := 0; c_bw := b |} Hb Hbuf He HL HD)
      as [st' [Hloop [Hz' Hv']]].
    rewrite (cb_loop_fuel_mono (S (length toks)) (Z.to_nat symnext + 1)
               sym symnext lt dt _ st' ltac:(lia) Hloop).
    cbv beta iota.
    destruct (zbits_send_code END_BLOCK lt (c_bw st') Hv' Heob) as [Hz Hv].
    split; [|exact Hv].
    rewrite Hz, Hz'. cbn [c_bw]. ring.
Qed.

(* ==========================================================================
   5.  The regroup: token sum = frequency-weighted symbol sum.
   ========================================================================== *)

Lemma g6_wsum_zero : forall (f : Z -> Z) lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> f i = 0) ->
  wsum f lo n = 0.
Proof.
  intros f lo n; revert lo; induction n as [|n IH]; intros lo Hz;
    cbn [wsum]; [reflexivity|].
  rewrite (Hz lo ltac:(rewrite Nat2Z.inj_succ; lia)).
  rewrite (IH (lo + 1)
             ltac:(intros i Hi; apply Hz; rewrite Nat2Z.inj_succ; lia)).
  ring.
Qed.

Lemma wsum_delta : forall (g : Z -> Z) x lo n,
  lo <= x < lo + Z.of_nat n ->
  wsum (fun i => (if Z.eqb x i then 1 else 0) * g i) lo n = g x.
Proof.
  intros g x lo n; revert lo; induction n as [|n IH]; intros lo Hx.
  - cbn [Z.of_nat] in Hx. lia.
  - cbn [wsum].
    destruct (Z.eqb_spec x lo) as [->|Ne].
    + cbv iota.
      rewrite (g6_wsum_zero
                 (fun i => (if Z.eqb lo i then 1 else 0) * g i) (lo + 1) n).
      * ring.
      * intros p Hp.
        replace (Z.eqb lo p) with false
          by (symmetry; apply Z.eqb_neq; lia).
        ring.
    + cbv iota.
      rewrite Z.mul_0_l, Z.add_0_l.
      apply IH. rewrite Nat2Z.inj_succ in Hx. lia.
Qed.

Lemma wsum_plus : forall f g lo n,
  wsum (fun i => f i + g i) lo n = wsum f lo n + wsum g lo n.
Proof.
  intros f g lo n; revert lo; induction n as [|n IH]; intro lo;
    cbn [wsum]; [ring|].
  rewrite IH. ring.
Qed.

Theorem toks_cost_regroup : forall lt dt toks,
  cEnc toks ->
  toks_cost lt dt toks
  = wsum (fun i => count_L i toks * cost_L lt i) 0 (Z.to_nat L_CODES)
    + wsum (fun i => count_D i toks * cost_D dt i) 0 (Z.to_nat D_CODES).
Proof.
  intros lt dt toks He.
  induction toks as [|t r IH].
  - cbn [toks_cost count_L count_D].
    rewrite (g6_wsum_zero (fun i => 0 * cost_L lt i) 0 (Z.to_nat L_CODES))
      by (intros; ring).
    rewrite (g6_wsum_zero (fun i => 0 * cost_D dt i) 0 (Z.to_nat D_CODES))
      by (intros; ring).
    ring.
  - inversion He as [|? ? Ht Hr]; subst.
    specialize (IH Hr).
    destruct t as [b | len dist].
    + (* literal: one count_L bump at b, count_D unchanged *)
      cbn [toks_cost tok_cost].
      destruct Ht as [Hb0 Hb1].
      rewrite (wsum_ext (fun i => count_L i (TLit b :: r) * cost_L lt i)
                 (fun i => (if Z.eqb b i then 1 else 0) * cost_L lt i
                           + count_L i r * cost_L lt i)
                 0 (Z.to_nat L_CODES))
        by (intros p _; cbn [count_L]; ring).
      rewrite (wsum_ext (fun i => count_D i (TLit b :: r) * cost_D dt i)
                 (fun i => count_D i r * cost_D dt i)
                 0 (Z.to_nat D_CODES))
        by (intros p _; cbn [count_D]; ring).
      rewrite wsum_plus.
      rewrite (wsum_delta (fun i => cost_L lt i) b 0 (Z.to_nat L_CODES))
        by (unfold L_CODES; lia).
      replace (cost_L lt b) with (t_len lt b).
      2:{ unfold cost_L.
          replace (Z.leb (LITERALS + 1) b) with false
            by (symmetry; apply Z.leb_gt; unfold LITERALS; lia).
          ring. }
      rewrite IH. ring.
    + (* match: one count_L bump at the length code, one count_D bump *)
      cbn [toks_cost tok_cost].
      destruct Ht as [[Hl0 Hl1] [Hd0 Hd1]].
      unfold MIN_MATCH in Hl0. unfold MAX_MATCH in Hl1.
      destruct (lcode_range (len - 3) ltac:(lia)) as [Hc _].
      destruct (DcodeRange_all (dist - 1) ltac:(lia)) as [Hdc _].
      rewrite (wsum_ext (fun i => count_L i (TMatch len dist :: r) * cost_L lt i)
                 (fun i => (if Z.eqb (length_code (len - 3) + LITERALS + 1) i
                            then 1 else 0) * cost_L lt i
                           + count_L i r * cost_L lt i)
                 0 (Z.to_nat L_CODES))
        by (intros p _; cbn [count_L]; ring).
      rewrite (wsum_ext (fun i => count_D i (TMatch len dist :: r) * cost_D dt i)
                 (fun i => (if Z.eqb (d_code (dist - 1)) i then 1 else 0)
                             * cost_D dt i
                           + count_D i r * cost_D dt i)
                 0 (Z.to_nat D_CODES))
        by (intros p _; cbn [count_D]; ring).
      rewrite !wsum_plus.
      rewrite (wsum_delta (fun i => cost_L lt i)
                 (length_code (len - 3) + LITERALS + 1) 0 (Z.to_nat L_CODES))
        by (unfold L_CODES, LITERALS in *; lia).
      rewrite (wsum_delta (fun i => cost_D dt i)
                 (d_code (dist - 1)) 0 (Z.to_nat D_CODES))
        by (unfold D_CODES in *; lia).
      replace (cost_L lt (length_code (len - 3) + LITERALS + 1))
        with (t_len lt (length_code (len - 3) + LITERALS + 1)
              + extra_lbits (length_code (len - 3))).
      2:{ unfold cost_L.
          replace (Z.leb (LITERALS + 1) (length_code (len - 3) + LITERALS + 1))
            with true
            by (symmetry; apply Z.leb_le; unfold LITERALS in *; lia).
          replace (length_code (len - 3) + LITERALS + 1 - (LITERALS + 1))
            with (length_code (len - 3)) by ring.
          reflexivity. }
      replace (cost_D dt (d_code (dist - 1)))
        with (t_len dt (d_code (dist - 1)) + extra_dbits (d_code (dist - 1)))
        by (unfold cost_D; reflexivity).
      rewrite IH. ring.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions compress_block_len.
Print Assumptions toks_cost_regroup.
Print Assumptions tok_cost_nonneg.
