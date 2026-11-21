(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtDecHsel — the Hsel composition
      (q7-decode lane, rootshape wave, 2026-08-20)

    [hsel_from_carried] discharges GtDecCost's [Hsel] Section premise
    from ReachSt's CARRIED clauses plus exactly ONE new fact,
    [lcode_root_opshape] — here a Section Variable [Hroot] standing in
    for the future LenTblSide clause (delivered at M_LEN by [rm_tblL]
    once the LenTblSide/DynTblOk wave lands; established on the dynamic
    path by a new [DynTblOk] field from an earlier development run's coverage, on the
    fixed path by [lenfix_root_opshape] below).  [decode_*_modulo4] at
    the bottom put the two decode faces on Hroot + Hret + Hreenter +
    Hshape — [Hsel] is no longer a face premise.

    Gap census this file certifies (each Hsel conjunct's source):
      1 <= nb        — if_wf_tbl's bits-floor clause at the masked root
                       index (index_range clause 1 at a dummy reader).
      0 <= c_val h   — rc_amb via [tbl_of_val_range] (any resolution).
      258-bound      — root: [Hroot] fires [lc_len_ok] (upto clause);
                       chained: [lcode_two_level] + the dummy-hold
                       [if_low_at] witness force op&16<>0, no census
                       needed at level 2 at all. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepPres.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtInfTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DeclIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRepro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecPump.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecCost.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecSel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecTbl.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The ONE missing carried fact: masked-root op-shape discrimination.
       (This exact text becomes the LenTblSide clause; an earlier development run inhabits
       its DynTblOk field against it.  No let-in: unfolds cleanly.)
   ========================================================================== *)

Definition lcode_root_opshape (t : ztbl) (rb : Z) : Prop :=
  forall x,
    c_op (t (Z.land x (Z.shiftl 1 rb - 1))) <> 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 240 <> 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 32 = 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 64 = 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 16 <> 0.

(* ==========================================================================
   2.  Bit-subset helpers (240 = 16 + 32 + 64 + 128).
   ========================================================================== *)

Lemma land240_sub : forall a, Z.land a 240 = 0 ->
  Z.land a 16 = 0 /\ Z.land a 64 = 0.
Proof.
  intros a H. split.
  - replace 16 with (Z.land 240 16) by reflexivity.
    rewrite Z.land_assoc, H. reflexivity.
  - replace 64 with (Z.land 240 64) by reflexivity.
    rewrite Z.land_assoc, H. reflexivity.
Qed.

(* ==========================================================================
   3.  The fixed-path arm: [lenfix] satisfies the clause, reflectively
       (mirrors [lenfix_tblside]; table-WIDE, so the masked-index form
       follows by instantiation).
   ========================================================================== *)

Definition chk_root_opshape (e : Code) : bool :=
  (c_op e =? 0) || (Z.land (c_op e) 240 =? 0)
  || negb (Z.land (c_op e) 32 =? 0) || negb (Z.land (c_op e) 64 =? 0)
  || negb (Z.land (c_op e) 16 =? 0).

Lemma chk_root_opshape_sound : forall e, chk_root_opshape e = true ->
  c_op e <> 0 -> Z.land (c_op e) 240 <> 0 -> Z.land (c_op e) 32 = 0 ->
  Z.land (c_op e) 64 = 0 -> Z.land (c_op e) 16 <> 0.
Proof.
  intros e H Hop H240 H32 H64. unfold chk_root_opshape in H.
  repeat (apply orb_prop in H; destruct H as [H|H]).
  - apply Z.eqb_eq in H. contradiction.
  - apply Z.eqb_eq in H. contradiction.
  - rewrite negb_true_iff in H. apply Z.eqb_neq in H. congruence.
  - rewrite negb_true_iff in H. apply Z.eqb_neq in H. congruence.
  - rewrite negb_true_iff in H. apply Z.eqb_neq in H. exact H.
Qed.

Lemma lenfix_root_chk :
  forallb (fun t => chk_root_opshape (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma default_root_opshape : chk_root_opshape (code_of3 (0, 0, 0)) = true.
Proof. reflexivity. Qed.

Lemma lenfix_root_opshape : lcode_root_opshape lenfix 9.
Proof.
  intros x. apply chk_root_opshape_sound.
  unfold lenfix.
  apply (tbl_of_list_all _ _ lenfix_root_chk default_root_opshape).
Qed.

(* ==========================================================================
   4.  THE COMPOSITION: Hsel from carried clauses + the one new fact.
   ========================================================================== *)

Section HselDraft.

(** Stand-in for the future LenTblSide clause as [rm_tblL] will deliver
    it at M_LEN.  NOTHING ELSE is assumed beyond ReachSt. *)
Variable Hroot : forall q,
    ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
    lcode_root_opshape (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                       (t_lenbits (s_tab (q_st q))).

(** Conclusion shape VERBATIM = GtDecCost's [Hsel] Section premise. *)
Theorem hsel_from_carried : forall q h b2 nb,
    ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
    inf_decode sub_len (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
    1 <= nb
    /\ 0 <= c_val h
    /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 -> Z.land (c_op h) 64 = 0 ->
        3 <= c_val h
        /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258).
Proof.
  intros q h b2 nb HR Hm Hdec.
  pose proof HR as (HC & HM).
  pose proof HC as [Hpos Hb39 Hbytes Hho Hwin Hwnext Hwhave Hsane
                    Hlen0 Hinbud Hleftu Hlens Hbh Hbn Hbd Hamb].
  pose proof Hpos as (Hh & Hb & Hleft).
  assert (HL : LenTblSide q) by (apply (rm_tblL q HM); left; exact Hm).
  destruct HL as (Htbl & Hlcs & Htds & Hlt2 & Hdt2 & Hlbnd & Hlb & Hdb & Hroot0).
  destruct Htbl as ((n & Hup & Hir & HTW & HTL) & Hdw & Hcfl & Hcfd & Hd13).
  (* Alignment: the if_ctx/len_args projections ARE the state views. *)
  assert (Efl : f_lcode (if_ctx (len_args q))
                = tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
    by reflexivity.
  assert (Efm : f_lmask (if_ctx (len_args q))
                = Z.shiftl 1 (t_lenbits (s_tab (q_st q))) - 1)
    by reflexivity.
  assert (Eal : a_lcode (len_args q)
                = tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
    by reflexivity.
  unfold lcode_len_bounded_upto in Hup.
  unfold lcode_index_range in Hir. destruct Hir as (Hir1 & Hir2).
  unfold lcode_two_level in Hlt2.
  rewrite Efl in Hup, Hir2, Hlt2.
  rewrite Efm in Hir1, Hlt2.
  rewrite Eal in HTW.
  destruct (sel_decode_shape _ _ _ _ _ _ _ Hdec)
    as [ (bf & Eh & Enb & Esub)
       | (bf & bg & h0 & Eh0 & Esub & Eh & Enb & Hbgs) ].
  - (* ROOT case *)
    pose proof (Hir1 {| f_in := 0; f_out := 0; f_hold := br_hold bf;
                        f_bits := 0; f_buf := zzero |}) as Hidx.
    cbn [f_hold] in Hidx.
    split; [|split].
    + rewrite Enb, Eh. exact (proj1 (HTW _ Hidx)).
    + rewrite Eh. exact (proj1 (tbl_of_val_range _ _ Hamb _)).
    + intros Hop0 H32 H64.
      assert (H240 : Z.land (c_op h) 240 <> 0).
      { unfold sub_len in Esub. apply andb_false_iff in Esub.
        destruct Esub as [E|E].
        - rewrite negb_false_iff in E. apply Z.eqb_eq in E. contradiction.
        - apply Z.eqb_neq in E. exact E. }
      rewrite Eh in Hop0, H240, H32, H64 |- *.
      exact (Hup _ Hidx (Hroot q HR Hm (br_hold bf) Hop0 H240 H32 H64)).
  - (* CHAINED case *)
    assert (Hbg0 : 0 <= br_hold bg).
    { apply Hbgs; [exact Hho | exact Hb
                  | intros j; exact (proj1 (Hbytes j))]. }
    unfold sub_len in Esub. apply andb_prop in Esub.
    destruct Esub as [Ea Eb].
    rewrite negb_true_iff in Ea. apply Z.eqb_neq in Ea.
    apply Z.eqb_eq in Eb.
    pose proof (land240_sub _ Eb) as (H16z & H64z).
    assert (Ech : lc_chains (c_op h0) = true).
    { unfold lc_chains. rewrite H16z, H64z.
      destruct (Z.eqb_spec (c_op h0) 0) as [E|_]; [contradiction|].
      reflexivity. }
    pose proof (Hir1 {| f_in := 0; f_out := 0; f_hold := br_hold bf;
                        f_bits := 0; f_buf := zzero |}) as Hidx0.
    cbn [f_hold] in Hidx0.
    assert (Hb0 : 1 <= c_bits h0 <= 15).
    { rewrite Eh0. exact (HTW _ Hidx0). }
    pose proof (chain_low_bounds (c_bits h0) (c_op h0) (br_hold bg)
                  ltac:(lia) Hbg0) as (HL0 & HLlt).
    assert (Hcase : c_op h0 < 0
                    \/ Z.shiftr (Z.land (br_hold bg)
                          (Z.shiftl 1 (c_bits h0 + c_op h0) - 1)) (c_bits h0)
                       < Z.shiftl 1 (c_op h0)).
    { destruct (Z.lt_ge_cases (c_op h0) 0) as [Hn|Hp];
        [left; exact Hn | right; exact (HLlt Hp)]. }
    pose proof (if_low_at (c_op h0) _ HL0 Hcase) as Eifl.
    (* two_level at the root read, dummy reader holding the low part *)
    pose proof (Hlt2 _ (br_hold bf)
                  {| f_in := 0; f_out := 0;
                     f_hold := Z.shiftr (Z.land (br_hold bg)
                                  (Z.shiftl 1 (c_bits h0 + c_op h0) - 1))
                                  (c_bits h0);
                     f_bits := 0; f_buf := zzero |} eq_refl) as H2l.
    rewrite <- Eh0 in H2l.
    specialize (H2l Ech).
    rewrite Eifl in H2l.
    rewrite <- Eh in H2l.
    (* index_range clause 2 puts the chained index below n *)
    pose proof (Hir2 _ {| f_in := 0; f_out := 0;
                     f_hold := Z.shiftr (Z.land (br_hold bg)
                                  (Z.shiftl 1 (c_bits h0 + c_op h0) - 1))
                                  (c_bits h0);
                     f_bits := 0; f_buf := zzero |} Hidx0) as Hidx1.
    rewrite <- Eh0 in Hidx1.
    specialize (Hidx1 Ech).
    rewrite Eifl in Hidx1.
    split; [|split].
    + rewrite Enb.
      assert (Hwh : 0 <= c_bits h)
        by (rewrite Eh; exact (proj1 (proj1 (tbl_of_tblside _ _ Hamb _)))).
      lia.
    + rewrite Eh. exact (proj1 (tbl_of_val_range _ _ Hamb _)).
    + intros Hop0 H32 H64.
      destruct (Z.eqb_spec (Z.land (c_op h) 16) 0) as [E16|E16].
      * exfalso. unfold lc_chains in H2l.
        rewrite E16 in H2l.
        assert (E1 : (c_op h =? 0) = false) by (apply Z.eqb_neq; exact Hop0).
        assert (E2 : (Z.land (c_op h) 64 =? 0) = true)
          by (apply Z.eqb_eq; exact H64).
        rewrite E1, E2 in H2l. cbn in H2l. discriminate.
      * rewrite Eh in E16 |- *.
        exact (Hup _ Hidx1 E16).
Qed.

End HselDraft.

(* ==========================================================================
   5.  THE FACES, modulo4: Hsel replaced by the one carried-clause
       stand-in.  When the LenTblSide/DynTblOk wave lands, Hroot's
       discharge is a one-line [rm_tblL] projection and the decode
       faces stand on Hret + Hreenter + Hshape alone.
   ========================================================================== *)

Theorem decode_raw_modulo4 :
  forall (Hroot : forall q,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             lcode_root_opshape
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_raw.
Proof.
  intros Hroot Hret Hreenter Hshape.
  exact (decode_raw_modulo3 (hsel_from_carried Hroot) Hret Hreenter Hshape).
Qed.

Theorem decode_auto_modulo4 :
  forall (Hroot : forall q,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             lcode_root_opshape
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_auto.
Proof.
  intros Hroot Hret Hreenter Hshape.
  exact (decode_auto_modulo3 (hsel_from_carried Hroot) Hret Hreenter Hshape).
Qed.
