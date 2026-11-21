(** * ZReproG6P — the bound-fit capstone, PARAMETRIC over the frame.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    q5-emitter's gzip face landed as a structural TWIN of the zlib one
    (ZR_GzPack: 10-byte header, avail_out = zr_deflate_bound 31 - 10,
    trailer room 8, wrap 2).  This file generalizes part L's BoundFit
    Section over the three frame constants — bound [B], header bytes
    [hdr], trailer room [troom] — so every (config x seam) instance of
    the bound-fit falls out of ONE argument:

      zlib: B = zr_deflate_bound 15, hdr = 2,  troom = 4, hdr+troom = 6
      gzip: B = zr_deflate_bound 31, hdr = 10, troom = 8, hdr+troom = 18

    In both rows [hdr + troom = zr_wraplen wb] — the wrap length IS
    header plus trailer — so the parametric room hypothesis
    [zlen x + 5*hnblocks + (hdr + troom) <= B] is exactly part I's
    room lemma at the config's wraplen: the shifts core
    [5*hnblocks <= shifts + 7] is wb-independent.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  SwWin SwEv SwStep G3Event ZRepro ZReproG6A ZReproG6I ZReproG6K
  ZReproG6L.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The room lemma at the gzip wraplen (wb-31 twin of part I's).
   ========================================================================== *)

Lemma zr_room_bound31 : forall len, 0 <= len < ZR_MAX_INPUT ->
  len + 5 * zr_hnblocks len + 18 <= zr_deflate_bound 31 len.
Proof.
  intros len Hlen.
  unfold ZR_MAX_INPUT in Hlen.
  unfold zr_deflate_bound, zr_wraplen.
  replace (31 <? 0) with false by reflexivity.
  replace (15 <? 31) with true by reflexivity.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (2 ^ 12) with 4096 by reflexivity.
  replace (2 ^ 14) with 16384 by reflexivity.
  replace (2 ^ 25) with 33554432 by reflexivity.
  pose proof (zr_room_shifts len Hlen) as Hr.
  lia.
Qed.

(* ==========================================================================
   2.  The parametric capstone.
   ========================================================================== *)

Section BoundFitP.

  Variable x : list Z.
  Variable evs : list FlushEv.
  Variable bw0 bwf : BW.
  Variable out0 outf : list Z.
  Variable avo0 avof : Z.

  (** the frame constants: total budget, header bytes, trailer room *)
  Variable B hdr troom : Z.

  Hypothesis Hx : 0 <= zlen x < ZR_MAX_INPUT.
  Hypothesis Hhdr : 0 <= hdr.

  Hypothesis Hchain : EvChain evs bw0 out0 avo0 bwf outf avof.
  (** the input position the last block reached; a prefix in general *)
  Variable T : Z.
  Hypothesis HT : 0 <= T <= zlen x.
  Hypothesis Htile : EvTile evs 0 T.
  Hypothesis Hbudget : Forall EvStepBudget evs.
  Hypothesis Hblocks : Z.of_nat (length evs) <= zr_hnblocks (zlen x).

  (** the body starts on a drained writer right after the header *)
  Hypothesis Hout0 : zlen out0 = hdr.
  Hypothesis Hbw0  : zbits bw0 = 0.
  Hypothesis Havo0 : avo0 = B - hdr.

  (** the frame's room: input + per-block stored overhead + frame bytes
      fit the budget (= part I's room lemma at the config's wraplen) *)
  Hypothesis Hroom : zlen x + 5 * zr_hnblocks (zlen x) + (hdr + troom) <= B.

  Theorem zr_bound_fits_p : troom <= avof.
  Proof.
    pose proof (zlen_nonneg x) as Hxn.
    destruct (evchain_ceil8 evs bw0 out0 avo0 bwf outf avof 0 T
                Hchain Htile
                (Forall_impl _ evstep_to_evbudget Hbudget))
      as [_ Hceil].
    destruct (evchain_avo evs bw0 out0 avo0 bwf outf avof Hchain Hbudget)
      as [Havof Hgrow].
    assert (Hstart : cb_tot bw0 out0 = 8 * hdr)
      by (unfold cb_tot; rewrite Hout0, Hbw0; ring).
    rewrite Hstart in Hceil.
    replace (ceil8 (8 * hdr)) with (8 * hdr) in Hceil.
    2:{ symmetry. apply ceil8_aligned.
        replace (8 * hdr) with (hdr * 8) by ring.
        apply Z_mod_mult. }
    pose proof (ceil8_ge (cb_tot bwf outf)) as Hcg.
    pose proof (zbits_nonneg bwf) as Hbf.
    assert (Hcb : 8 * zlen outf <= cb_tot bwf outf)
      by (unfold cb_tot; lia).
    assert (Houtf : zlen outf <= B - troom).
    { assert (Hbnd : 8 * zlen outf
                     <= 8 * hdr + 8 * (T - 0) + 40 * Z.of_nat (length evs))
        by lia.
      assert (Hblk8 : 40 * Z.of_nat (length evs)
                      <= 40 * zr_hnblocks (zlen x)) by lia.
      unfold zr_hnblocks in *. lia. }
    rewrite Havof, Hout0, Havo0. lia.
  Qed.

  Corollary zr_needmore_refuted_p : 0 < troom -> avof = 0 -> False.
  Proof. intros Ht H0. pose proof zr_bound_fits_p. lia. Qed.

End BoundFitP.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions zr_bound_fits_p.
Print Assumptions zr_room_bound31.
Unset Printing All.
