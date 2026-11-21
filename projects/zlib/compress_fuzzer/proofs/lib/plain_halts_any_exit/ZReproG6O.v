(** * ZReproG6O — ZR_SpanSeam's per-event discharge: the stored guard
    cannot pass at a 16-bit-overflowing span.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    THE SEAM (q5-emitter's ZR_SpanGuard, verbatim consumer): if the block
    has a stored option ([0 <= blockstart]) and the stored guard
    [span + 4 <= opt_lenb] PASSES, then [span < 65536] — i.e.
    [tr_stored_block]'s 16-bit length field cannot overflow on the arm
    the code actually takes.

    THE ARGUMENT, all landed pieces: [opt_lenb <= static_lenb] by the
    min-choice (either branch of the if); [8 * static_lenb <= SL + 10];
    the g6-slupper clause gives [SL <= toks_cost(static) + EOB + 64];
    every static token costs at most 31 bits (literal <= 9; match
    <= 8 + 5 + 5 + 13 — the crude cap, no TOO_FAR needed); and memLevel 8
    caps the tally at 16383 tokens.  So
    [span <= (31*16383 + 15 + 64 + 10)/8 - 4 = 63501] — under 65536 with
    ~2000 bytes to spare.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees DeflateSpec CbEmit CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  SwWin SwEv G3Event ZReproG6A ZReproG6C ZReproG6G ZReproG6H ZReproG6N
  ZREmitBody.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The crude static cap: every token costs at most 31 bits.
   ========================================================================== *)

(** Length-code side of a match: code bits + length extras cap at 13. *)
Definition g6o_lc13_at (c : Z) : bool :=
  t_len static_ltree (c + LITERALS + 1) + extra_lbits c <=? 13.

Lemma g6o_lc13_all : forallb g6o_lc13_at (zseq 29 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma g6o_tok_cap : forall t,
  tok_enc t -> tok_cost static_ltree static_dtree t <= 31.
Proof.
  intros t He. destruct t as [b | len dist].
  - cbn [tok_cost]. cbn [tok_enc] in He.
    pose proof (forallb_zseq' g6n_lit_at 256 256 b
                  ltac:(vm_compute; reflexivity) g6n_lit_all He) as H.
    unfold g6n_lit_at in H. apply Z.leb_le in H. lia.
  - cbn [tok_cost]. cbn [tok_enc] in He.
    destruct He as [Hlen Hdist].
    unfold MIN_MATCH, MAX_MATCH in Hlen.
    destruct (DcodeRange_all (dist - 1) ltac:(lia)) as (Hdc & _ & _).
    set (dc := d_code (dist - 1)) in *.
    pose proof (forallb_zseq' g6n_d5_at 30 30 dc
                  ltac:(vm_compute; reflexivity) g6n_d5_all Hdc) as H5.
    unfold g6n_d5_at in H5. apply Z.eqb_eq in H5.
    pose proof (forallb_zseq' g6n_dex_at 30 30 dc
                  ltac:(vm_compute; reflexivity) g6n_dex_all Hdc) as H13.
    unfold g6n_dex_at in H13. apply Z.leb_le in H13.
    destruct (lcode_range (len - 3) ltac:(lia)) as (Hlc & _ & _).
    set (c := length_code (len - 3)) in *.
    pose proof (forallb_zseq' g6o_lc13_at 29 29 c
                  ltac:(vm_compute; reflexivity) g6o_lc13_all Hlc) as HL.
    unfold g6o_lc13_at in HL. apply Z.leb_le in HL.
    lia.
Qed.

Lemma g6o_toks_cap : forall toks,
  cEnc toks ->
  toks_cost static_ltree static_dtree toks <= 31 * Z.of_nat (length toks).
Proof.
  induction toks as [|t r IH]; intro He.
  - cbn. lia.
  - inversion He as [|? ? Het Her]; subst.
    cbn [toks_cost length].
    pose proof (g6o_tok_cap t Het). pose proof (IH Her).
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* ==========================================================================
   2.  The per-event guard discharge.
   ========================================================================== *)

Theorem span_guard_holds : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g ->
  dg_sym_end g <= 49149 ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  ZR_SpanGuard ev.
Proof.
  intros g wrap done ev HE Hlev Hsend Hol0 Hsl0 Hbl0 HblZ HnnL HnnD.
  intros Hbs Hguard.
  destruct HE as (Ecfg & Ewrap & Hbuf & Hfreq & Henc & Hsn & Hspan & Hend
                  & Hres & Hspan_eq & Hwin & Hlast01).
  set (s := fe_s ev) in *.
  assert (Hlen : Z.of_nat (length (fe_toks ev)) <= 16383).
  { pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext. lia. }
  destruct (dispatch_counters (d_ts s) (fe_toks ev) Hol0 Hsl0 Hbl0 Hfreq Henc
              Hlen HblZ HnnL HnnD)
    as (OL & SL & EOL & ESL & HOLr & HSLr & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & _ & _ & _ & HSLup).
  (* the guard's byte counters, in plain Z *)
  assert (Estatlenb : u64 (ts_statlen (snd (build_bl_tree (build_tree TK_D
                        (build_tree TK_L (d_ts s))))) + 3 + 7) / 8
                      = (SL + 10) / 8).
  { rewrite ESL. f_equal. unfold u64. rewrite Z.mod_small by lia. ring. }
  assert (Eoptlenb : u64 (ts_optlen (snd (build_bl_tree (build_tree TK_D
                       (build_tree TK_L (d_ts s))))) + 3 + 7) / 8
                     = (OL + 10) / 8).
  { rewrite EOL. f_equal. unfold u64. rewrite Z.mod_small by lia. ring. }
  rewrite Estatlenb, Eoptlenb in Hguard.
  apply Z.leb_le in Hguard.
  (* both if-branches sit at or under the static byte count *)
  set (SLB := (SL + 10) / 8) in *.
  set (OLB := (OL + 10) / 8) in *.
  assert (Hoptb : ls_strstart (d_ls s) - ls_blockstart (d_ls s) + 4 <= SLB).
  { destruct ((SLB <=? OLB) || (dg_strategy (d_cfg s) =? Z_FIXED)) eqn:Eif.
    - exact Hguard.
    - apply orb_false_iff in Eif as [Eif _].
      apply Z.leb_gt in Eif. lia. }
  (* the static counter is capped by the crude per-token bound *)
  assert (Hcost : toks_cost static_ltree static_dtree (fe_toks ev)
                  <= 31 * 16383).
  { pose proof (g6o_toks_cap (fe_toks ev) Henc). lia. }
  assert (Heob : 0 <= t_len static_ltree END_BLOCK <= 15).
  { unfold END_BLOCK. apply static_ltree_LenB. lia. }
  assert (HSLcap : SL <= 31 * 16383 + 15 + 64) by lia.
  assert (HSLBcap : SLB <= 63496).
  { unfold SLB.
    apply Z.div_le_upper_bound; lia. }
  rewrite <- Hspan_eq in Hoptb.
  lia.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions g6o_toks_cap.
Print Assumptions span_guard_holds.
Unset Printing All.
