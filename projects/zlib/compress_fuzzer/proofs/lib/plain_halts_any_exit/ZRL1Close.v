(** * ZRL1Close — the Case-B hole is DISCHARGED: zr_l1_min_fits holds.

    OWNER: l1-adversary (2026-08-23). Composition fit-check: consumes
    huffman-opt's landed zr_l1_dyn_fits (bed ZHOBed.ZHOCaseB, PA-closed,
    independently gate-verified) through the RIGHT disjunct of
    ZRL1FastNone.zr_l1_min_fits — the one-liner the handoff designed.

    AT SPLICE: the two [From ZHOBed]/[ZRL1Bed] imports become
    [From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ...] at the
    landed module names; nothing else changes (iface-twin lesson: this
    file is the FIT-CHECK at the frozen spellings; the path migration is
    the window's mechanical edit).

    With this, the whole (1,-15) buf=None per-event budget follows from
    walk-side facts alone: flush_from_acct_full_fast +
    zr_l1_min_fits_holds close the last mathematical hole of the fast
    face. TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees DeflateSpec CbEmit CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BuildTree SendGo SendGoWf SendItems ClStream HuffCover ScanCount.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  BtFrame SwWin SwEv SwStep G3Event G3DynA ZReproG6A ZReproG6C ZReproG6D
  ZReproG6I ZReproG6K ZReproG6L ZReproG6F ZReproG6G ZReproG6H ZReproG6N.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRL1FastNone.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOCaseB.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Theorem zr_l1_min_fits_holds : forall ts toks slen,
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  toks_ext toks = slen ->
  32506 < slen ->
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  zr_l1_min_fits ts slen.
Proof.
  intros ts toks slen Henc Hlen Hext Hslen Hol Hsl Hbl HFI HblZ HnnL HnnD.
  right.
  exact (zr_l1_dyn_fits ts toks slen Henc Hlen Hext Hslen Hol Hsl Hbl
           HFI HblZ HnnL HnnD).
Qed.

(** The fast tr-level theorem with the hole GONE (premises = G6N's minus
    TOO_FAR; conclusion identical). *)
Theorem tr_flush_block_len_none_fast_closed :
  forall ts toks slen last level dtype,
  bwv (ts_bw ts) ->
  last = 0 \/ last = 1 ->
  0 < level ->
  BufToks (ts_symbuf ts) 0 (ts_symnext ts) toks ->
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  toks_ext toks = slen ->
  32506 < slen ->
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  let ts' := snd (tr_flush_block None slen last level 0 dtype ts) in
  zbits (ts_bw ts) <= zbits (ts_bw ts')
  /\ ceil8 (zbits (ts_bw ts'))
     <= ceil8 (zbits (ts_bw ts)) + 8 * slen + 40
  /\ bwv (ts_bw ts')
  /\ (last = 1 -> bw_valid (ts_bw ts') = 0).
Proof.
  intros ts toks slen last level dtype
         Hbwv Hl Hlevel Hbuf Henc Hntoks Hext Hsld
         Hol0 Hsl0 Hbl0 HFI HblZ HnnL HnnD.
  apply (tr_flush_block_len_none_fast ts toks slen last level dtype
           Hbwv Hl Hlevel Hbuf Henc Hntoks Hext Hsld
           Hol0 Hsl0 Hbl0 HFI HblZ HnnL HnnD).
  exact (zr_l1_min_fits_holds ts toks slen Henc Hntoks Hext Hsld
           Hol0 Hsl0 Hbl0 HFI HblZ HnnL HnnD).
Qed.

Print Assumptions zr_l1_min_fits_holds.
Print Assumptions tr_flush_block_len_none_fast_closed.
