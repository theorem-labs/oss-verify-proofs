(** * W5D14 — the 1.4 twin of W5D.
    The producer of the FROZEN A1StmtsV3_14.ZrLenDynLeg14_STMT over RT's
    1.4 flavour.  Text twin of W5D.v by tools/gen_twin14.py; by hand: the imports and the gate split, which now has
    three conjuncts (the third, bits < 8, is not used: the fast branch is the same text, and the 1.4 gate premise
    rewrites inf_LEN14's own test).  The one-step shape is W5D's word for word. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge Inflate14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream
  W3Trip W4Fold W5Bridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3 A1StmtsV3_14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W3D W4D.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Theorem w5d_leg14 : ZrLenDynLeg14_STMT.
Proof.
  unfold ZrLenDynLeg14_STMT.
  intros c q ll dl entl entd HVl HVd HownL HownD HrL HrD Hle Hde Hpl Hpd
         Hrop Hwf Hput Hleft Htie Hcap Hwh Hsn Hm Hg Halb Hhcap.
  (* the guard, split *)
  pose proof Hg as Hg2.
  apply andb_prop in Hg2. destruct Hg2 as (Hg2 & _).
  apply andb_prop in Hg2. destruct Hg2 as (Hg6 & Hg258).
  apply Z.leb_le in Hg6. apply Z.leb_le in Hg258.
  pose proof Hwf as (Hwb & Hwh2 & Hwhave & Hwbytes).
  (* (a)/(b): the ctx pack and the entry pack at inf_LEN's record *)
  assert (Hpack : w4d_ctxpack (if_ctx (w5_args q))
                    (t_lenbits (s_tab (q_st q)))
                    (t_distbits (s_tab (q_st q))) ll dl entl entd).
  { unfold w4d_ctxpack.
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
  pose proof (w4d_if_model (w5_args q) (q_br q)
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
    destruct HM as (HLen & HType & _).
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
    + (* ExBad -> BAD *)
      right; right; left. exists 1%nat, (w5_qB q y m).
      assert (EI : inf_iter14 1 c q
                   = match inf_step14 c q with
                     | InfCont q' => Some q'
                     | _ => None
                     end) by reflexivity.
      rewrite Estep in EI.
      split; [exact EI | reflexivity].
  - (* fuel: the fourth arm absorbs it *)
    try rewrite EM in Estep; cbv beta iota in Estep.
    right; right; right. exists 1%nat, InfFuel.
    assert (EL2 : inf_loop14 1 c q
                  = match inf_step14 c q with
                    | InfCont q' => inf_loop14 0 c q'
                    | r => Some r
                    end) by reflexivity.
    rewrite Estep in EL2.
    split; [exact EL2 | exact I].
Qed.

Print Assumptions w5d_leg14.
