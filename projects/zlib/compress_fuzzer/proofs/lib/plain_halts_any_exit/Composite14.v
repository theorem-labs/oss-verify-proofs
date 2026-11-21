(* the zlib 1.4 twin of Composite, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from Composite), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * Composite — ZrHuffDynLeg's SYMBOLS HALF, assembled (dyn round,
      q7-decode Leg A4; freeze doc v9 ).

    [zr_huff_dyn_holds : ZrCodesFetchRes -> ZrHuffDynLeg] modulo the
    Section Variables below — an earlier development run's in-flight B3/B5 exports carried
    in their MINIMAL CONSUMABLE form (the hsel_from_carried/Hroot
    pattern): when their proofs land, instantiation is one application.

    VARIABLE <-> EXPORT MAP (the round's final convergence checklist;
    db_acc RESOLUTION per freeze v11 — seam finding #1 CLOSED:
    g1 weakened the B3 heads db_ok -> db_acc, bed , heads
    ; Hamb_dispatch DELETED):
      Hlen_export   <- g1 dyn_two_own_len_STMT at db_acc, BUNDLED with
                       the LEN pins (freeze v9 bundling option); the
                       it_pre/it_entry context is g1's proof device, not
                       consumed here, so this Variable is implied by
                       their export whichever pins-wiring lands.
      Hdist_export  <- g1 dyn_two_own_dist_STMT at db_acc, same bundling.
      Hlenbits_acc  <- g1 dyn_lenbits_acc (proven in their bed, additive)
      Hdistbits_acc <- g1 dyn_distbits_acc (proven, additive)
      Hroot_acc     <- g1 dyn_root_opshape_acc (additive-in-flight, same
                       fix pattern as the range lemmas — the landed
                       dyn_root_opshape_holds premises db_ok and nothing
                       reconstructs it reach-free)
    B5 facts consumed as LANDED citations (no Variables):
      decode_dynamic_tables_valid/_sizes/_le (DeflateSpec), the v5
      population bounds + list ties + frames (zr_len_dispatch conjuncts,
      landed Q6TblChain ).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inftrees Inflate
  InflateThy StepReach DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  Q6TblChain Q6HuffResidue GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  A1StmtsV3 A1core A1trip A1loop W5D.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require B3Asm B3B5Stmts GtCodesRes.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Composite.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1loop14 A1trip14 Q6HuffResidue14 Q6TblChain14 Spec.PngModel.Inflate14 Spec.PngModel.Inflate14Iter W5D14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Section CompositeAsm.

(** g1 B3 LEN export at db_acc, minimal consumable form (header map).
    Amendment (a) (freeze v32): + the PreGo premise, spelled verbatim as
    the zr_len_dispatch conjunct; placed at the END of the telescope
    (g1's lane snapshot predates the amendment; the discharge is
    order-insensitive — the application passes the dispatch's own Hpre1). *)
Variable Hlen_export : forall d q' (lit dst : list nat),
    db_acc d -> db_installed d q' ->
    db_lens d = zlens (lit ++ dst) ->
    db_nlen d = Z.of_nat (length lit) ->
    db_ndist d = Z.of_nat (length dst) ->
    db_nlen d <= 286 ->
    db_ndist d <= 30 ->
    (exists c1 st1, it_pre CT_LENS (db_lens d) (db_nlen d) 9
                      (fun i => db_cs d (0 + i)) = PreGo c1 st1) ->
    exists entl,
      zr_two_own_v3
        (tbl_of (q_st q') (t_lencode (s_tab (q_st q'))))
        (o_bits (db_o1 d)) lit entl
      /\ zr_len_ents lit entl.

(** g1 B3 DIST export at db_acc, same form. *)
Variable Hdist_export : forall d q' (lit dst : list nat),
    db_acc d -> db_installed d q' ->
    db_lens d = zlens (lit ++ dst) ->
    db_nlen d = Z.of_nat (length lit) ->
    db_ndist d = Z.of_nat (length dst) ->
    db_nlen d <= 286 ->
    db_ndist d <= 30 ->
    exists entd,
      zr_two_own_v3
        (tbl_of (q_st q') (t_distcode (s_tab (q_st q'))))
        (o_bits (db_o2 d)) dst entd
      /\ zr_dist_ents dst entd.

(** g1's additive db_acc-tier range/shape lemmas (bed ; land as
    one-line instantiations). *)
Variable Hlenbits_acc : forall d, db_acc d -> 1 <= o_bits (db_o1 d) <= 15.
Variable Hdistbits_acc : forall d, db_acc d -> 1 <= o_bits (db_o2 d) <= 15.
Variable Hroot_acc : forall d q',
    db_acc d -> db_installed d q' ->
    GtDecHsel.lcode_root_opshape
      (tbl_of (q_st q') (t_lencode (s_tab (q_st q'))))
      (t_lenbits (s_tab (q_st q'))).

Theorem zr_huff_dyn_holds14 : ZrCodesFetchRes -> ZrHuffDynLeg14.
Proof.
  intros HBridge.
  unfold ZrHuffDynLeg14.
  intros c q Hc Hwf Hha Hbud Hput Hleft Htie Hcap Hwh Hsn Hret Hm.
  destruct (zr_table_chain_holds14 HBridge c q Hc Hwf Hha Hput Hm Hret)
    as [ (lit & dst & r3 & qL & d & HD0 & HSL & HwfL & HhaL & Hdisp)
       | [ HBAD | HEXIT ] ];
    [ | right; left; exact HBAD | right; right; exact HEXIT ].
  destruct Hdisp as (Hstep & Hacc & Hinst & Hlens & Hnl & Hnd & Hb1
                     & Hb2 & Hpre1 & Hpre2 & Hob & Hlast & Hin & Hout
                     & Hwsz & HretL & Hwrap & Hflags & Hcheck & Htotal
                     & HwhL & HsaneL).
  destruct (Hlen_export d qL lit dst Hacc Hinst Hlens Hnl Hnd Hb1 Hb2
              Hpre1)
    as (entl & Hownl & Hpinsl).
  destruct (Hdist_export d qL lit dst Hacc Hinst Hlens Hnl Hnd Hb1 Hb2)
    as (entd & Hownd & Hpinsd).
  pose proof Hinst as (Il & Ilb & Id & Idb & Icodes).
  set (qm := qmode qL M_LEN).
  (* qm-side facts, each by CONVERSION from the qL/q facts *)
  assert (Ilbm : t_lenbits (s_tab (q_st qm)) = o_bits (db_o1 d))
    by exact Ilb.
  assert (Idbm : t_distbits (s_tab (q_st qm)) = o_bits (db_o2 d))
    by exact Idb.
  assert (Hownl' : zr_two_own_v3
            (tbl_of (q_st qm) (t_lencode (s_tab (q_st qm))))
            (t_lenbits (s_tab (q_st qm))) lit entl)
    by (rewrite Ilbm; exact Hownl).
  assert (Hownd' : zr_two_own_v3
            (tbl_of (q_st qm) (t_distcode (s_tab (q_st qm))))
            (t_distbits (s_tab (q_st qm))) dst entd)
    by (rewrite Idbm; exact Hownd).
  assert (Hlb' : 0 < t_lenbits (s_tab (q_st qm)) <= 15)
    by (rewrite Ilbm; pose proof (Hlenbits_acc d Hacc); lia).
  assert (Hdb' : 0 < t_distbits (s_tab (q_st qm)) <= 15)
    by (rewrite Idbm; pose proof (Hdistbits_acc d Hacc); lia).
  assert (Hpopl : (length lit <= 286)%nat) by lia.
  assert (Hpopd : (length dst <= 30)%nat) by lia.
  destruct (decode_dynamic_tables_valid _ _ _ _ HD0) as (Vl & Vd).
  assert (Hshm : GtDecHsel.lcode_root_opshape
            (tbl_of (q_st qm) (t_lencode (s_tab (q_st qm))))
            (t_lenbits (s_tab (q_st qm))))
    by (exact (Hroot_acc d qL Hacc Hinst)).
  assert (HAL : inf_step14 c q = inf_step14 c qm).
  { rewrite (zr_step14_at_len c qm ltac:(reflexivity)). exact Hstep. }
  (* reader facts at qm *)
  assert (Eob : q_ob qm = q_ob q) by exact Hob.
  assert (Eout : q_out qm = q_out q) by exact Hout.
  assert (HwfL' : br_wf (q_br qm)) by exact HwfL.
  assert (HhaL' : W2Stream.br_haligned (q_br qm)) by exact HhaL.
  assert (Hput' : 0 <= o_put (q_ob qm)) by (rewrite Eob; exact Hput).
  assert (Hleft' : 0 <= o_left (q_ob qm)) by (rewrite Eob; exact Hleft).
  assert (Htie' : q_out qm = o_put (q_ob qm) + o_left (q_ob qm))
    by (rewrite Eout, Eob; exact Htie).
  assert (Hcap' : q_out qm <= 4294967295) by (rewrite Eout; exact Hcap).
  assert (Ewh : w_whave (s_win (q_st qm)) = w_whave (s_win (q_st q)))
    by exact HwhL.
  assert (Hwh' : w_whave (s_win (q_st qm)) = 0) by (rewrite Ewh; exact Hwh).
  assert (Esn : t_sane (s_tab (q_st qm)) = t_sane (s_tab (q_st q)))
    by exact HsaneL.
  assert (Hsn' : t_sane (s_tab (q_st qm)) <> 0) by (rewrite Esn; exact Hsn).
  assert (ESm : br_stream (q_br qm) = r3) by exact HSL.
  assert (Hbud' : br_have (q_br qm) + br_bits (q_br qm) / 8 <= 4294967290).
  { pose proof (decode_dynamic_tables_le _ _ _ _ HD0) as Hle3.
    assert (HlenS : (length (br_stream (q_br qm))
                     <= length (br_stream (q_br q)))%nat)
      by (rewrite ESm; exact Hle3).
    pose proof (br_budget_mono (q_br q) (q_br qm) Hwf HwfL' HlenS) as HBM.
    lia. }
  (* the agreement head *)
  left. exists lit, dst, r3.
  split. { exact HD0. }
  unfold zr_huff_exit14.
  destruct (zr_sym_loop_dyn14 (S (length (br_stream (q_br qm)))) c qm
              lit dst entl entd w5d_leg14 Vl Vd Hownl' Hownd' Hlb' Hdb'
              Hpinsl Hpinsd Hpopl Hpopd Hshm
              ltac:(lia) HwfL' Hput' Hleft' Htie' Hcap' Hwh' Hsn'
              ltac:(reflexivity) HhaL' Hbud')
    as [ (k & q' & syms & rem & HI & HD & HS & HR & HM & C6 & C7 & C8
          & C9 & C10 & C11 & C12 & C13 & CF & CK & CT & C14 & C15 & C16
          & CH)
       | [ (k & q' & HI & HM) | (n2 & sx & HL & HX) ] ].
  - (* agreement *)
    left.
    destruct k as [|k'].
    { exfalso. cbn [inf_iter14] in HI. injection HI as <-.
      assert (HmM : h_mode (s_hdr (q_st qm)) = M_LEN) by reflexivity.
      rewrite HmM in HM. discriminate. }
    exists (S k'), q', syms, rem.
    split. { exact (inf_iter14_alias_S c q qm k' q' HAL HI). }
    split. { rewrite <- ESm. exact HD. }
    split. { exact HS. }
    split. { exact C6. }
    split. { rewrite <- Eob. exact HR. }
    split. { rewrite <- Eob. exact C9. }
    split. { exact C7. }
    split. { exact C8. }
    split. { exact HM. }
    split. { assert (El : h_last (s_hdr (q_st qm)) = h_last (s_hdr (q_st q)))
               by exact Hlast.
             rewrite <- El. exact C12. }
    (* zr_blk_frame q q' : in/out/ret/wsize/wrap/flags/whave/sane *)
    assert (Ein : q_in qm = q_in q) by exact Hin.
    assert (EretL : q_ret qm = 0) by exact HretL.
    assert (Ewrap : h_wrap (s_hdr (q_st qm)) = h_wrap (s_hdr (q_st q)))
      by exact Hwrap.
    assert (Eflags : h_flags (s_hdr (q_st qm)) = h_flags (s_hdr (q_st q)))
      by exact Hflags.
    assert (Echeck : h_check (s_hdr (q_st qm)) = h_check (s_hdr (q_st q)))
      by exact Hcheck.
    assert (Etotal : h_total (s_hdr (q_st qm)) = h_total (s_hdr (q_st q)))
      by exact Htotal.
    assert (Ewsz : w_wsize (s_win (q_st qm)) = w_wsize (s_win (q_st q)))
      by exact Hwsz.
    assert (Hbud2 : br_have (q_br q') + br_bits (q_br q') / 8
                    <= 4294967290).
    { pose proof (decode_symbols_shorter _ _ _ _ _ HD) as HLn.
      pose proof (br_budget_mono (q_br qm) (q_br q') HwfL' C6
                    ltac:(rewrite HS; lia)) as HBM2.
      lia. }
    split.
    { split. { rewrite C15. exact Ein. }
      split. { rewrite C16. exact Eout. }
      split. { rewrite C14, EretL, Hret. reflexivity. }
      split. { rewrite C11. exact Ewsz. }
      split. { rewrite C13. exact Ewrap. }
      split. { rewrite CF. exact Eflags. }
      split. { rewrite CK. exact Echeck. }
      split. { rewrite CT. exact Etotal. }
      split. { rewrite C11. exact Ewh. }
      rewrite C10. exact Esn. }
    split. { exact CH. }
    exact Hbud2.
  - (* BAD *)
    right; left.
    destruct k as [|k'].
    { exfalso. cbn [inf_iter14] in HI. injection HI as <-.
      assert (HmM : h_mode (s_hdr (q_st qm)) = M_LEN) by reflexivity.
      rewrite HmM in HM. discriminate. }
    exists (S k'), q'.
    split; [ exact (inf_iter14_alias_S c q qm k' q' HAL HI) | exact HM ].
  - (* EXIT *)
    right; right.
    destruct n2 as [|n']; [cbn [inf_loop14] in HL; discriminate|].
    exists (S n'), sx.
    split; [ exact (inf_loop14_alias_S c q qm n' sx HAL HL) |].
    destruct sx as [qx|qx|qx r| |]; try exact HX.
    assert (EretL : q_ret qm = 0) by exact HretL.
    rewrite Hret, HX, EretL. reflexivity.
Qed.

End CompositeAsm.


(* ==========================================================================
   THE INSTANTIATION (final train): the five Variables at g1's landed
   names + model-rt's bridge production (GtCodesRes).
   ========================================================================== *)

(** Adapter: the landed LEN head (amendment-(a) telescope, fused pins,
    existential-with-context) implies the composite's minimal form —
    destruct-and-repackage, the context/tie conjuncts dropped. *)

(** THE ROUND'S SENTENCE. *)
Theorem zr_huff_dyn_leg_holds14 : ZrHuffDynLeg14.
Proof.
  exact (zr_huff_dyn_holds14
           hlen_export_landed
           B3Asm.dyn_two_own_dist
           B3B5Stmts.dyn_lenbits_acc
           B3B5Stmts.dyn_distbits_acc
           B3B5Stmts.dyn_root_opshape_acc
           GtCodesRes.zr_codes_fetch_res_holds).
Qed.

