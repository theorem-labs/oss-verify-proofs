(* the zlib 1.4 twin of LkFastDyn, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from LkFastDyn), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * LkFastDyn — the DYN fast leg, GOOD-ONLY (fuel arm killed)
    (q7-decode leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    [W5DSel.w5d_leg_sel]'s statement (fastsel2 bed) minus the fourth
    (leave/fuel) arm, with ONE new premise: the whave-0 totality
    context [LkBody.lk_ctx_wf0] at the fast gate (at built tables it
    is NOT derivable from pins; the K3 assembly discharges it from
    DynTblOkHolds' db_ok/db_installed package).  Proof is W5DSel's
    dispatcher verbatim with the [if_model = None] branch REFUTED by
    [lk_if_model_total0].

    Also carries [lk_ctx0_transport]: the context package rides
    s_tab/s_win preservation, which is how the dyn loop re-arms it at
    each iterate.

    PA-EXPORTS: lk_ctx0_transport, lk_fast_leg_dyn_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream
  W3Trip W4Fold W5Bridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W3DSel W4DSel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Ents.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkBody.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkFastDyn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The context package rides the walk's table/window preservation. *)

(** The dyn fast leg, good-only: band and first three arms verbatim
    from W5DSel's ZrLenDynLegSelTight_STMT, plus the totality context. *)
Theorem lk_fast_leg_dyn_good14 :
  forall c q (ll dl : list nat) (entl entd : nat -> Code),
    ValidLengths ll 15%nat ->
    ValidLengths dl 15%nat ->
    zr_two_own_v3 (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) ll entl ->
    zr_two_own_v3 (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
        (t_distbits (s_tab (q_st q))) dl entd ->
    0 < t_lenbits (s_tab (q_st q)) <= 15 ->
    0 < t_distbits (s_tab (q_st q)) <= 15 ->
    zr_len_ents3 ll entl ->
    zr_dist_ents1 dl entd ->
    (length ll <= 286)%nat ->
    (length dl <= 30)%nat ->
    GtDecHsel.lcode_root_opshape
        (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) ->
    lk_ctx_wf0 (if_ctx (w5_args q)) ->
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
    (exists k q' p rem,
       inf_iter14 k c q = Some q'
       /\ zr_syms_prefix ll dl (br_stream (q_br q)) p rem
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
    \/ (exists k q' p rem,
       inf_iter14 k c q = Some q'
       /\ zr_syms_prefix ll dl (br_stream (q_br q)) p rem
       /\ decode_lit_len ll dl rem = Some (LzEnd, br_stream (q_br q'))
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
        /\ (decode_symbols ll dl (br_stream (q_br q)) = None
            \/ (exists syms rem,
                  decode_symbols ll dl (br_stream (q_br q))
                  = Some (syms, rem)
                  /\ resolve_lz syms (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                     = None))).
Proof.
  intros c q ll dl entl entd HVl HVd HownL HownD HrL HrD Hle Hde Hpl Hpd
         Hrop Hctx0 Hwf Hput Hleft Htie Hcap Hwh Hsn Hm Hg Halb Hhcap.
  (* the guard, split *)
  pose proof Hg as Hg2.
  (* 1.4: the gate's third conjunct (bits < 8) is not needed below *)
  apply andb_prop in Hg2. destruct Hg2 as (Hg2 & _).
  apply andb_prop in Hg2. destruct Hg2 as (Hg6 & Hg258).
  apply Z.leb_le in Hg6. apply Z.leb_le in Hg258.
  pose proof Hwf as (Hwb & Hwh2 & Hwhave & Hwbytes).
  (* (a)/(b): the ctx pack and the entry pack at inf_LEN's record *)
  assert (Hpack : w4dsel_ctxpack (if_ctx (w5_args q))
                    (t_lenbits (s_tab (q_st q)))
                    (t_distbits (s_tab (q_st q))) ll dl entl entd).
  { unfold w4dsel_ctxpack.
    split; [exact HVl|]. split; [exact HVd|].
    split; [exact HownL|]. split; [exact HownD|].
    split; [exact Hle|]. split; [exact Hde|].
    split; [exact Hpl|]. split; [exact Hpd|].
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
  pose proof (w4dsel_if_model (w5_args q) (q_br q)
                (t_lenbits (s_tab (q_st q))) (t_distbits (s_tab (q_st q)))
                ll dl entl entd Hpack Hent Hwf Halb Hg6 Hhcap
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
    destruct (lk_if_model_total0 (w5_args q) Hctx0) as (y & Hy).
    rewrite EM in Hy. discriminate.
Qed.

Set Printing Width 2000.
