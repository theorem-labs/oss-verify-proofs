(* the zlib 1.4 twin of LkFast, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from LkFast), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * LkFast — the FIXED fast leg, GOOD-ONLY (fuel arm killed)
    (q7-decode leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    [W5Sel.zr_len_fast_leg_fix_sel]'s statement
    ([Gap7FixSel.ZrLenFastLegFixSel_STMT]) minus the fourth
    (leave/fuel) arm: premise band and the CONT/ENDED/BAD arms are
    byte-verbatim from Gap7FixSel.v (bed copy, statement md5 recorded
    in the fixsel bed).  The proof is W5Sel's dispatcher verbatim,
    with the [if_model = None] branch REFUTED by LkBody's whave-0
    totality ([lk_if_model_total0] at [lk_fixed_ctx0]) instead of
    absorbed into an arm — the one arm-4 emission site the 4-arm proof
    has.

    PA-EXPORT: lk_fast_leg_fix_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream
  W3Trip W4Fold W5Bridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import FixSelCore W3Sel
  W4Sel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M ZReproQ6R.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7FixSel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkBody.
(* LAST import: pins the statement's [br_stream] to ZReproQ6A's (the
   ratified statements' vocabulary); ZBitsBridge's twin is convertible
   ([zr_stream_eq] is [reflexivity]), so the W5Sel-mirror proof's
   [exact]s cross by conversion. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The whave-0 context contract at the fast gate, from the band's own
    pins (fixed tables). *)

(** The fast leg, good-only: band and first three arms byte-verbatim
    from [Gap7FixSel.ZrLenFastLegFixSel_STMT]. *)
Theorem lk_fast_leg_fix_good14 :
  forall c q (entl entd : nat -> Code),
    t_lencode (s_tab (q_st q)) = TRlenfix ->
    t_lenbits (s_tab (q_st q)) = 9 ->
    t_distcode (s_tab (q_st q)) = TRdistfix ->
    t_distbits (s_tab (q_st q)) = 5 ->
    ValidLengths fixed_lit_lengths 15%nat ->
    ValidLengths fixed_dist_lengths 15%nat ->
    ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) fixed_lit_lengths 15%nat entl ->
    ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
        (t_distbits (s_tab (q_st q))) fixed_dist_lengths 15%nat entd ->
    0 < t_lenbits (s_tab (q_st q)) <= 15 ->
    0 < t_distbits (s_tab (q_st q)) <= 15 ->
    (forall sym cw, code_for fixed_lit_lengths 15%nat sym = Some cw ->
         sub_len (entl sym) = false) ->
    (forall sym cw, code_for fixed_dist_lengths 15%nat sym = Some cw ->
         sub_dist (entd sym) = false) ->
    zr_len_ents fixed_lit_lengths entl ->
    zr_dist_ents fixed_dist_lengths entd ->
    GtDecHsel.lcode_root_opshape
        (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) ->
    br_wf (q_br q) ->
    0 <= o_put (q_ob q) ->
    0 <= o_left (q_ob q) ->
    q_out q = o_put (q_ob q) + o_left (q_ob q) ->
    q_out q <= 4294967295 ->
    w_whave (s_win (q_st q)) = 0 ->
    t_sane (s_tab (q_st q)) <> 0 ->
    h_mode (s_hdr (q_st q)) = M_LEN ->
    (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8) = true ->
    W2Stream.br_haligned (q_br q) ->
    br_have (q_br q) <= 4294967290 ->
    (* CONT: a nonempty prefix consumed, back at M_LEN *)
    (exists k q' p rem,
       inf_iter14 k c q = Some q'
       /\ zr_syms_prefix fixed_lit_lengths fixed_dist_lengths
            (br_stream (q_br q)) p rem
       /\ p <> []
       /\ br_stream (q_br q') = rem
       /\ (length rem < length (br_stream (q_br q)))%nat
       /\ resolve_lz p (ob_slice (q_ob q) 0 (o_put (q_ob q)))
          = Some (ob_slice (q_ob q') 0 (o_put (q_ob q')))
       /\ h_mode (s_hdr (q_st q')) = M_LEN
       /\ br_wf (q_br q')
       /\ 0 <= o_put (q_ob q')
       /\ 0 <= o_left (q_ob q')
       /\ o_put (q_ob q') + o_left (q_ob q')
          = o_put (q_ob q) + o_left (q_ob q)
       /\ s_tab (q_st q') = s_tab (q_st q)
       /\ s_win (q_st q') = s_win (q_st q)
       /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
       /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
       /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
       /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
       /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
       /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
       /\ W2Stream.br_haligned (q_br q'))
    (* ENDED: a prefix plus the end-of-block, block done at M_TYPE *)
    \/ (exists k q' p rem,
       inf_iter14 k c q = Some q'
       /\ zr_syms_prefix fixed_lit_lengths fixed_dist_lengths
            (br_stream (q_br q)) p rem
       /\ decode_lit_len fixed_lit_lengths fixed_dist_lengths rem
          = Some (LzEnd, br_stream (q_br q'))
       /\ resolve_lz p (ob_slice (q_ob q) 0 (o_put (q_ob q)))
          = Some (ob_slice (q_ob q') 0 (o_put (q_ob q')))
       /\ h_mode (s_hdr (q_st q')) = M_TYPE
       /\ br_wf (q_br q')
       /\ 0 <= o_put (q_ob q')
       /\ 0 <= o_left (q_ob q')
       /\ o_put (q_ob q') + o_left (q_ob q')
          = o_put (q_ob q) + o_left (q_ob q)
       /\ s_tab (q_st q') = s_tab (q_st q)
       /\ s_win (q_st q') = s_win (q_st q)
       /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
       /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
       /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
       /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
       /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
       /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
       /\ W2Stream.br_haligned (q_br q'))
    \/ (exists k q',
        inf_iter14 k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD
        /\ zr_fix_dec_failure q).
Proof.
  intros c q entl entd Hpin1 Hpin2 Hpin3 Hpin4 HVl HVd HownL HownD
         HrL HrD Hsubl Hsubd Hle Hde Hrop Hwf Hput Hleft Htie Hcap Hwh
         Hsn Hm Hg Halb Hhcap.
  (* the invalid-corner packs, from the statement's own ownership at the
     pinned concrete tables *)
  assert (Hviewl : tbl_of (q_st q) (t_lencode (s_tab (q_st q))) = lenfix)
    by (rewrite Hpin1; reflexivity).
  assert (Hviewd : tbl_of (q_st q) (t_distcode (s_tab (q_st q))) = distfix)
    by (rewrite Hpin3; reflexivity).
  assert (HownLf : ZReproQ6M.zr_root_own lenfix 9 fixed_lit_lengths
                     15%nat entl)
    by (rewrite <- Hviewl, <- Hpin2; exact HownL).
  assert (HownDf : ZReproQ6M.zr_root_own distfix 5 fixed_dist_lengths
                     15%nat entd)
    by (rewrite <- Hviewd, <- Hpin4; exact HownD).
  pose proof (zr_invl_own entl HownLf) as Hinvl.
  pose proof (zr_invd_own entd HownDf) as Hinvd.
  (* the guard, split *)
  pose proof Hg as Hg2.
  (* 1.4: the gate's third conjunct (bits < 8) is not needed below *)
  apply andb_prop in Hg2. destruct Hg2 as (Hg2 & _).
  apply andb_prop in Hg2. destruct Hg2 as (Hg6 & Hg258).
  apply Z.leb_le in Hg6. apply Z.leb_le in Hg258.
  pose proof Hwf as (Hwb & Hwh2 & Hwhave & Hwbytes).
  (* (a)/(b): the ctx pack and the entry pack at inf_LEN's record *)
  assert (Hpack : w4sel_ctxpack (if_ctx (w5_args q))
                    (t_lenbits (s_tab (q_st q)))
                    (t_distbits (s_tab (q_st q)))
                    fixed_lit_lengths fixed_dist_lengths entl entd).
  { unfold w4sel_ctxpack.
    split; [exact HVl|]. split; [exact HVd|].
    split; [exact HownL|]. split; [exact HownD|].
    split; [exact Hle|]. split; [exact Hde|].
    split; [exact Hinvl|]. split; [exact Hinvd|].
    split; [exact HrL|]. split; [exact HrD|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hwh|]. split; [exact Hsn|].
    split; [intros i; exact (Hwbytes i)|].
    assert (Ee : f_end (if_ctx (w5_args q))
                 = o_put (q_ob q) + (o_left (q_ob q) - 257))
      by reflexivity.
    lia. }
  assert (Hent : w4_entry_pack (w5_args q) (q_br q)).
  { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (w2_restore_hold q) | exact (w2_restore_bits q)]. }
  assert (Hsumcap : a_next_out (w5_args q) + a_avail_out (w5_args q)
                    <= 4294967295).
  { assert (En : a_next_out (w5_args q) = o_put (q_ob q)) by reflexivity.
    assert (El : a_avail_out (w5_args q) = o_left (q_ob q)) by reflexivity.
    lia. }
  pose proof (w4sel_if_model (w5_args q) (q_br q)
                (t_lenbits (s_tab (q_st q))) (t_distbits (s_tab (q_st q)))
                fixed_lit_lengths fixed_dist_lengths entl entd
                Hpack Hent Hwf Halb Hg6 Hhcap
                Hput Hg258 Hsumcap Htie) as HM.
  (* (c): the one-step shape of inf_LEN's fast branch *)
  assert (Estep : inf_step14 c q
          = match if_model (w5_args q) with
            | None => InfFuel
            | Some y =>
                InfCont (match y_exit y with
                         | ExLen => w5_qL q y
                         | ExType => w5_qT q y
                         | ExBad m => w5_qB q y m
                         end)
            end).
  { unfold inf_step14, q_mode. rewrite Hm. cbv iota.
    unfold inf_LEN14. cbv zeta. rewrite Hg. cbv iota.
    unfold w5_qL, w5_qT, w5_qB, w5_args, w5_q3.
    match goal with
    | |- context[if_model ?A] => destruct (if_model A) as [y|]
    end; [|reflexivity].
    destruct (y_exit y) as [| |m].
    - match goal with
      | |- context[q_mode (q_load ?Q3)] =>
          assert (Em5 : q_mode (q_load Q3) = M_LEN) by exact Hm
      end.
      rewrite Em5. reflexivity.
    - match goal with
      | |- context[q_mode (q_load (qmode ?Q3 M_TYPE))] =>
          assert (Em5 : q_mode (q_load (qmode Q3 M_TYPE)) = M_TYPE)
            by reflexivity
      end.
      rewrite Em5. reflexivity.
    - match goal with
      | |- context[q_mode (q_load (qbad ?Q3 m))] =>
          assert (Em5 : q_mode (q_load (qbad Q3 m)) = M_BAD)
            by reflexivity
      end.
      rewrite Em5. reflexivity. }
  (* (d)/(e): dispatch on the model's answer and the exit *)
  pose proof (w5_model_availout_nonneg (w5_args q)) as HAO.
  destruct (if_model (w5_args q)) as [y|] eqn:EM.
  - try rewrite EM in HM; cbv beta iota in HM.
    try rewrite EM in HAO; cbv beta iota in HAO.
    destruct HM as (HLen & HType & HBad).
    try rewrite EM in Estep; cbv beta iota in Estep.
    destruct (y_exit y) as [| |m] eqn:EX;
      try rewrite EX in Estep; cbv beta iota in Estep.
    + (* ExLen -> CONT *)
      destruct (HLen eq_refl)
        as (p & rem & Hpre & Hpne & Hstr & Hlen & Hres & Hbwf & Hbal
            & Hyout & Hsum').
      assert (Hyo2 : o_put (q_ob q) <= y_out y) by exact Hyout.
      left. exists 1%nat, (w5_qL q y), p, rem.
      assert (EI : inf_iter14 1 c q
                   = match inf_step14 c q with
                     | InfCont q' => Some q'
                     | _ => None
                     end) by reflexivity.
      rewrite Estep in EI.
      split; [exact EI|].
      split; [exact Hpre|].
      split; [exact Hpne|].
      split; [exact Hstr|].
      split; [exact Hlen|].
      split; [exact Hres|].
      split; [exact Hm|].
      split; [exact Hbwf|].
      split; [change (0 <= y_out y); lia|].
      split; [change (0 <= y_avail_out y); exact HAO|].
      split; [change (y_out y + y_avail_out y
                      = o_put (q_ob q) + o_left (q_ob q));
              exact Hsum'|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      exact Hbal.
    + (* ExType -> ENDED *)
      destruct (HType eq_refl)
        as (p & rem & Hpre & Hend & Hres & Hbwf & Hbal & Hyout & Hsum').
      assert (Hyo2 : o_put (q_ob q) <= y_out y) by exact Hyout.
      right; left. exists 1%nat, (w5_qT q y), p, rem.
      assert (EI : inf_iter14 1 c q
                   = match inf_step14 c q with
                     | InfCont q' => Some q'
                     | _ => None
                     end) by reflexivity.
      rewrite Estep in EI.
      split; [exact EI|].
      split; [exact Hpre|].
      split; [exact Hend|].
      split; [exact Hres|].
      split; [reflexivity|].
      split; [exact Hbwf|].
      split; [change (0 <= y_out y); lia|].
      split; [change (0 <= y_avail_out y); exact HAO|].
      split; [change (y_out y + y_avail_out y
                      = o_put (q_ob q) + o_left (q_ob q));
              exact Hsum'|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      exact Hbal.
    + (* ExBad -> BAD, exporting the declarative failure *)
      right; right. exists 1%nat, (w5_qB q y m).
      assert (EI : inf_iter14 1 c q
                   = match inf_step14 c q with
                     | InfCont q' => Some q'
                     | _ => None
                     end) by reflexivity.
      rewrite Estep in EI.
      split; [exact EI|].
      split; [reflexivity|].
      exact (HBad m eq_refl).
  - (* fuel: REFUTED by the whave-0 totality *)
    exfalso.
    destruct (lk_if_model_total0 (w5_args q)
                (lk_fixed_ctx0 q Hpin1 Hpin2 Hpin3 Hpin4 Hwh Hsn))
      as (y & Hy).
    rewrite EM in Hy. discriminate.
Qed.

Set Printing Width 2000.
