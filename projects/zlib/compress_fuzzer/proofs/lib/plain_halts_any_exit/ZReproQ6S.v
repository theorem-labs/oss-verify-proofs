(** * ZReproQ6S — the CONDITIONAL fixed-leg discharge:
    [ZrLenFastLeg -> ZrHuffFixedLeg] (LEN-chain layer 4b).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).

    The residue's dispatch state is [M_LEN_]; its step IS the [M_LEN]
    step of the mode-adjusted state (fallthrough aliasing), so the loop
    runs there and every projection transfers by conversion.  The one
    open input is the fast-path residue [ZrLenFastLeg] — once its
    discharge lands, [ZrHuffFixedLeg] follows by composition.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6P ZReproQ6Q ZReproQ6R Q6HuffResidue
  ZReproL0E.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* amendment window 2 (q7-decode per TL grant 2026-08-20; owner review
   trails): ZrLenFastLeg gained the br_haligned + input-budget premises
   (negotiation items 5 and 7 — without them the fast leg is falsifiable,
   see the countermodels in a working folder
   0445.md).  The unconditional [ZrLenFastLeg -> ZrHuffFixedLeg] of the
   pre-amend2 file is therefore not derivable as stated; the theorem is
   restated at the ALIGNED variant, which carries the two premises.
   ZrHuffFixedLeg itself (Q6HuffResidue, q6-fixedtbl surface) is
   untouched; the unconditional composition returns when the fleet
   settles the br_haligned carrier (vacuous at bits<8 states, so the
   walk-level discharges are one vm/lemma each). *)
Definition ZrHuffFixedLegAligned : Prop :=
  forall c q,
    zr_cflush_ok c ->
    br_wf (q_br q) ->
    0 <= o_put (q_ob q) ->
    0 <= o_left (q_ob q) ->
    q_out q = o_put (q_ob q) + o_left (q_ob q) ->
    q_out q <= 4294967295 ->
    w_whave (s_win (q_st q)) = 0 ->
    t_sane (s_tab (q_st q)) <> 0 ->
    h_mode (s_hdr (q_st q)) = M_LEN_ ->
    t_lencode (s_tab (q_st q)) = TRlenfix ->
    t_lenbits (s_tab (q_st q)) = 9 ->
    t_distcode (s_tab (q_st q)) = TRdistfix ->
    t_distbits (s_tab (q_st q)) = 5 ->
    W2Stream.br_haligned (q_br q) ->
    br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
    zr_huff_exit c q fixed_lit_lengths fixed_dist_lengths
                 (br_stream (q_br q)).

Theorem zr_fixed_from_fast : ZrLenFastLeg -> ZrHuffFixedLegAligned.
Proof.
  intros HFast c q Hc Hwf Hput Hleft Htie Hcap Hwh Hsn Hm HpL HpLb HpD
         HpDb Hha Hbud.
  set (qm := qmode q M_LEN).
  assert (Hviewl : tbl_of (q_st qm) (t_lencode (s_tab (q_st qm)))
                   = lenfix).
  { assert (HpLm : t_lencode (s_tab (q_st qm)) = TRlenfix) by exact HpL.
    rewrite HpLm. reflexivity. }
  assert (Hviewd : tbl_of (q_st qm) (t_distcode (s_tab (q_st qm)))
                   = distfix).
  { assert (HpDm : t_distcode (s_tab (q_st qm)) = TRdistfix) by exact HpD.
    rewrite HpDm. reflexivity. }
  assert (Hrootl : t_lenbits (s_tab (q_st qm)) = 9) by exact HpLb.
  assert (Hrootd : t_distbits (s_tab (q_st qm)) = 5) by exact HpDb.
  assert (Hshm : GtDecHsel.lcode_root_opshape
            (tbl_of (q_st qm) (t_lencode (s_tab (q_st qm))))
            (t_lenbits (s_tab (q_st qm)))).
  { rewrite Hviewl, Hrootl. exact GtDecHsel.lenfix_root_opshape. }
  assert (HAL : inf_step c q = inf_step c qm).
  { rewrite (zr_step_at_len c qm ltac:(reflexivity)).
    unfold inf_step, q_mode. rewrite Hm.
    unfold inf_LEN_. reflexivity. }
  destruct (zr_sym_loop (S (length (br_stream (q_br qm)))) c qm
              fixed_lit_lengths fixed_dist_lengths zr_entl_fix zr_entd_fix
              HFast fixed_lit_valid fixed_dist_valid
              ltac:(rewrite Hviewl, Hrootl; exact zr_ownl_fix)
              ltac:(rewrite Hviewd, Hrootd; exact zr_ownd_fix)
              ltac:(rewrite Hrootl; lia)
              ltac:(rewrite Hrootd; lia)
              zr_subl_fix zr_subd_fix zr_entsl_fix zr_entsd_fix
              Hshm
              ltac:(lia) Hwf Hput Hleft Htie Hcap Hwh Hsn
              ltac:(reflexivity) Hha Hbud)
    as [ (k & q' & syms & rem & HI & HD & HS & HR & HM & C6 & C7 & C8
          & C9 & C10 & C11 & C12 & C13 & CF & CK & CT & C14 & C15 & C16
          & CH)
       | [ (k & q' & HI & HM) | (n2 & sx & HL & HX) ] ].
  - (* agreement *)
    left.
    destruct k as [|k'].
    { exfalso. cbn [inf_iter] in HI. injection HI as <-.
      assert (HmM : h_mode (s_hdr (q_st qm)) = M_LEN) by reflexivity.
      rewrite HmM in HM. discriminate. }
    exists (S k'), q', syms, rem.
    split. { exact (inf_iter_alias_S c q qm k' q' HAL HI). }
    split. { exact HD. }
    split. { exact HS. }
    split. { exact C6. }
    split. { exact HR. }
    split. { exact C9. }
    split. { exact C7. }
    split. { exact C8. }
    split. { exact HM. }
    split. { exact C12. }
    (* v4 tail: zr_blk_frame (now w/ flags after wrap), then the
       reader alignment and the compositional budget (amendment #10) *)
    assert (Hbud' : br_have (q_br q') + br_bits (q_br q') / 8
                    <= 4294967290).
    { pose proof (decode_symbols_shorter _ _ _ _ _ HD) as HLn.
      assert (HQM : br_stream (q_br qm) = br_stream (q_br q))
        by reflexivity.
      rewrite HQM in HLn.
      pose proof (br_budget_mono (q_br q) (q_br q') Hwf C6
                    ltac:(rewrite HS; lia)) as HBM.
      lia. }
    split.
    { split. { exact C15. }
      split. { exact C16. }
      split. { exact C14. }
      split. { rewrite C11. reflexivity. }
      split. { exact C13. }
      split. { exact CF. }
      split. { exact CK. }
      split. { exact CT. }
      split. { rewrite C11. reflexivity. }
      rewrite C10. reflexivity. }
    split. { exact CH. }
    exact Hbud'.
  - (* BAD *)
    right; left.
    destruct k as [|k'].
    { exfalso. cbn [inf_iter] in HI. injection HI as <-.
      assert (HmM : h_mode (s_hdr (q_st qm)) = M_LEN) by reflexivity.
      rewrite HmM in HM. discriminate. }
    exists (S k'), q'.
    split; [ exact (inf_iter_alias_S c q qm k' q' HAL HI) | exact HM ].
  - (* EXIT *)
    right; right.
    destruct n2 as [|n']; [cbn [inf_loop] in HL; discriminate|].
    exists (S n'), sx.
    split; [ exact (inf_loop_alias_S c q qm n' sx HAL HL) |].
    destruct sx as [qx|qx|qx r| |]; exact HX.
Qed.

Print Assumptions zr_fixed_from_fast.

(** amendment #10 (q7-decode as TL-confirmed carrier): the CANONICAL
    restatement — the residue's premise-carrying [ZrHuffFixedLeg]
    follows from the fast leg by the same composition, intros-reordered.
    The Aligned stopgap above is retained per the retention convention
    (superseded as the consumer spelling). *)
Theorem zr_fixed_canonical : ZrLenFastLeg -> ZrHuffFixedLeg.
Proof.
  intros HFast c q Hc Hwf Hha Hbud Hput Hleft Htie Hcap Hwh Hsn Hm HpL
         HpLb HpD HpDb.
  exact (zr_fixed_from_fast HFast c q Hc Hwf Hput Hleft Htie Hcap Hwh
           Hsn Hm HpL HpLb HpD HpDb Hha Hbud).
Qed.

Print Assumptions zr_fixed_canonical.
