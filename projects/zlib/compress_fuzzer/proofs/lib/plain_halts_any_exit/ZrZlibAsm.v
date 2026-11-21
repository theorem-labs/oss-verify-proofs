(** * ZrZlibAsm — zlib face assembly: init + entry step + body walk + tail.

    OWNER: q6-asm-copier (q6-fixedtbl lane, zlib z-repro campaign,
    2026-08-20).  v2 (amendment #10).  Shape copied from the GREEN
    ZrRawAsm.v / ZrGzipAsm.v; the footer composes the landed lemmas.

    Section hypotheses (all three discharged in the footer):

    1. [zr_body_walk_flags] — the walk with the amended [zr_body_exit]
       agreement arm inlined: the h_flags clause (after h_wrap) plus,
       at #10, the exit [br_haligned] / bit-budget exports appended
       last; the [zr_body_entry] premise gains the matching two
       conjuncts, discharged at the face's entry state below.
       Discharged by [ZReproQ6W.zr_body_walk_fuel] (post-#10
       [zr_body_exit] unfolds to exactly the inlined trichotomy).
    2. [zr_zl_tail_len] — [Q6ZlibTail.zr_zl_tail] v3 verbatim (br_wf
       premise; the 32-bit stream-length export in the Z_STREAM_END
       arm).
    3. [zr_dec_split] — [Q6DecSplit.dec_stream_split] verbatim (the
       byte-alignment premise on the suffix; the unrestricted form is
       FALSE, machine-checked in Q6DecSplit; the zlib trailer is the
       4-byte adler32, so the split suffix is byte-aligned).

    Also proved here (no gap): [zl_head_ret] — an [inf_step] from a
    non-raw M_HEAD state preserves [q_ret]; needed because
    [Q6ZlibEntry.zr_zl_entry]'s BAD/DICTID arms do not export the ret of
    their existential state (a fourth, MINOR statement gap, closed
    locally below rather than reported, since it needs no landed-file
    amendment).

    Remaining residue after [zr_zlib_core_final] = the two leg Props.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits BwStream ZBitsIn Huff DeflateSpec
  InflateFast Inflate Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproQ6A ZReproL0C ZReproL0E ZReproQ6I Q6AsmSupport
  Q6ZlibEntry Q6ZlibTail Q6DecSplit Q6HuffResidue ZReproQ6W.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Plumbing.
   ========================================================================== *)

Lemma zr_zl_q0 : forall enc cap,
  inf_st0 {| g_st := zr_zi0; g_state_null := false;
             g_z := zr_zz0; g_inbuf := zlist enc; g_next_in := 0;
             g_avail_in := zlen enc; g_in_null := false;
             g_outbuf := zzero; g_next_out := 0; g_avail_out := cap;
             g_out_null := false; g_flush := Z_FINISH; g_walloc := true;
             g_wfresh := zzero |}
  = zrq zr_zi0 zr_zz0 enc 0 zzero 0 cap.
Proof.
  intros enc cap.
  unfold inf_st0, zrq.
  cbn [g_st g_z g_inbuf g_next_in g_avail_in g_outbuf g_next_out
       g_avail_out zr_zi0 s_hdr h_mode s_hold s_bits].
  f_equal; f_equal; lia.
Qed.

(** [br_wf] of a zrq reader at any in-range position. *)
Lemma zr_zrq_brwf : forall st z stream nxt obuf put cap,
  0 <= nxt <= zlen stream ->
  Forall (fun b => 0 <= b < 256) stream ->
  br_wf (q_br (zrq st z stream nxt obuf put cap)).
Proof.
  intros st z stream nxt obuf put cap Hn HBy.
  unfold br_wf, zrq. cbn [q_br br_bits br_hold br_have br_in].
  refine (conj _ (conj _ (conj _ _))).
  - lia.
  - change (Z.shiftl 1 0) with 1. lia.
  - lia.
  - intros j. unfold zlist.
    destruct (Nat.lt_ge_cases (Z.to_nat j) (length stream)) as [Hlt|Hge].
    + rewrite Forall_forall in HBy. apply HBy, nth_In, Hlt.
    + rewrite nth_overflow by exact Hge. lia.
Qed.

(** A HEAD step of a wrapped (wrap <> 0) stream preserves [q_ret]: every
    [InfCont] arm of [inf_HEAD] is a setter tower over [q]. *)
Lemma zl_head_ret : forall c q q',
  h_mode (s_hdr (q_st q)) = M_HEAD ->
  h_wrap (s_hdr (q_st q)) <> 0 ->
  inf_step c q = InfCont q' ->
  q_ret q' = q_ret q.
Proof.
  intros c q q' Hm Hw H.
  unfold inf_step, q_mode in H. rewrite Hm in H.
  cbv beta iota in H.
  unfold inf_HEAD in H. cbv zeta in H.
  replace (h_wrap (s_hdr (q_st q)) =? 0) with false in H
    by (symmetry; apply Z.eqb_neq; exact Hw).
  cbv beta iota in H.
  destruct (inf_nb 16 (q_br q)) as [b|b]; cbv beta iota zeta in H.
  2:{ discriminate H. }
  repeat first
    [ discriminate H
    | (injection H as <-; reflexivity)
    | match type of H with context [if ?t then _ else _] =>
        destruct t; cbv beta iota zeta in H
      end ].
Qed.

Section ZlibAsm.

(** GAP 1 — the walk with the flags clause (marked) added to the
    agreement arm of [zr_body_exit], plus the #10 exit exports (marked)
    appended last; legs re-plumbed at discharge time exactly as
    ZrRawAsm's footer does. *)
Hypothesis zr_body_walk_flags : forall c q,
  zr_cflush_ok c ->
  zr_body_entry q ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  (exists k q' out,
     inf_iter k c q = Some q'
     /\ dec_stream_from (br_stream (q_br q))
          (ob_slice (q_ob q) 0 (o_put (q_ob q)))
        = Some (out, br_stream (q_br q'))
     /\ ob_slice (q_ob q') 0 (o_put (q_ob q')) = out
     /\ br_wf (q_br q')
     /\ 0 <= o_put (q_ob q')
     /\ 0 <= o_left (q_ob q')
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ h_mode (s_hdr (q_st q')) = M_TYPE
     /\ h_last (s_hdr (q_st q')) <> 0
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))  (* THE GAP *)
     (* amendment #11: h_check/h_total frame conjuncts — carrier
        q7-decode; g1 census; q6 pre-ruling;
        #10 shape *)
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
     /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
     /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
     /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
     /\ W2Stream.br_haligned (q_br q')                        (* #10 *)
     /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290)  (* #10 *)
  \/ (exists k q', inf_iter k c q = Some q'
        /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists n s, inf_loop n c q = Some s
        /\ match s with
           | InfLeave q2 => q_ret q2 = q_ret q
           | InfCont _ => False
           | InfRet _ _ => False
           | InfDead _ => False
           | InfFuel => True
           end).

(** GAP 2 — [Q6ZlibTail.zr_zl_tail] v3 verbatim (discharged in the
    footer). *)
Hypothesis zr_zl_tail_len : forall c q,
  zr_cflush_ok c ->
  h_wrap (s_hdr (q_st q)) = 5 ->
  h_flags (s_hdr (q_st q)) = 0 ->
  br_wf (q_br q) ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  h_last (s_hdr (q_st q)) <> 0 ->
  (exists n q'', inf_loop n c q = Some (InfLeave q'')
     /\ q_ret q'' = q_ret q)
  \/ (exists n q'', inf_loop n c q = Some (InfLeave q'')
     /\ q_ret q'' = Z_DATA_ERROR)
  \/ (exists n q'', inf_loop n c q = Some (InfLeave q'')
     /\ q_ret q'' = Z_STREAM_END
     /\ ob_slice (q_ob q'') 0 (o_put (q_ob q''))
        = ob_slice (q_ob q) 0 (o_put (q_ob q))
     /\ h_mode (s_hdr (q_st q'')) = M_DONE
     /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q))
     /\ (32 <= length (br_stream (q_br q)))%nat).

(** GAP 3 — [Q6DecSplit.dec_stream_split] verbatim (the byte-alignment
    premise; the unrestricted form is FALSE — see
    [Q6DecSplit.dec_stream_split_unrestricted_false]).  Discharged in
    the footer. *)
Hypothesis zr_dec_split : forall b1 b2 out rem,
  dec_stream_from (b1 ++ b2) [] = Some (out, rem) ->
  (length b2 <= length rem)%nat ->
  (exists k, length b2 = (8 * k)%nat) ->
  dec_stream b1 = Some out.

Theorem zr_zlib_core_asm : forall cap b0 b1 body ad y,
  0 <= cap ->
  cap <= 4294967295 ->
  zlen ([b0; b1] ++ body ++ be32 ad) <= 4294967290 ->
  Forall (fun b => 0 <= b < 256) ([b0; b1] ++ body ++ be32 ad) ->
  zr_inflate Z_FINISH 15 cap ([b0; b1] ++ body ++ be32 ad) = Some y ->
  dec_stream (bytes_bits body) = Some y.
Proof.
  intros cap b0 b1 body ad y Hc0 Hcap Henc HBy.
  set (rest := body ++ be32 ad) in *.
  assert (HBy' := HBy). rewrite Forall_forall in HBy'.
  assert (Hb0 : 0 <= b0 < 256) by (apply HBy'; now left).
  assert (Hb1 : 0 <= b1 < 256) by (apply HBy'; right; now left).
  unfold zr_inflate.
  rewrite zr_init_15'.
  unfold zr_inf_call, inflate_model.
  cbv beta iota zeta.
  cbn [g_state_null g_out_null g_in_null g_st g_z g_inbuf g_next_in
       g_avail_in g_outbuf g_next_out g_avail_out g_flush g_walloc
       g_wfresh orb andb negb].
  rewrite zr_zl_q0.
  match goal with |- context [inf_loop _ ?C _] => set (C0 := C) end.
  assert (HC0 : zr_cflush_ok C0).
  { unfold zr_cflush_ok, C0, inf_ctx. cbn [n_flush g_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  match goal with |- context [inf_loop ?F ?C ?Q] =>
    destruct (inf_loop F C Q) as [s|] eqn:ELOOP
  end;
  cbv beta iota;
  [ intro Hrun | discriminate ].
  (* the header step, three arms *)
  destruct (zr_zl_entry zr_zz0 b0 b1 rest zzero 0 cap Hb0 Hb1)
    as [ (q' & EN & HmB)
       | [ (q' & EN & HmD & HdD)
         | (z' & dm & EN) ] ];
  change zr_ic with C0 in EN;
  pose proof (inf_iter_one _ _ _ EN) as HE1.
  - (* BAD: one more step to the DATA_ERROR leave *)
    pose proof (zr_bad_absorb C0 q' HmB) as HBA.
    pose proof (inf_loop_after_iter 1 C0 _ q' 1 _ HE1 HBA) as HC.
    pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
    cbv beta iota in Hrun.
    destruct (inf_leave C0 (qset_ret q' Z_DATA_ERROR)) as [q3 r] eqn:ELV.
    try rewrite ELV in Hrun; cbv beta iota in Hrun.
    assert (Hne : r <> Z_STREAM_END).
    { pose proof (zr_leave_ret_ne C0 (qset_ret q' Z_DATA_ERROR)) as HNE.
      rewrite ELV in HNE. cbn [snd] in HNE.
      apply HNE.
      cbn [q_ret qset_ret].
      unfold Z_DATA_ERROR, Z_STREAM_END. lia. }
    cbn [r_ret r_q] in Hrun.
    rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hrun.
    discriminate Hrun.
  - (* DICTID: NEED_DICT ret or an out-of-input leave, both non-END *)
    assert (Hret' : q_ret q' = Z_OK).
    { rewrite (zl_head_ret C0
                 (zrq zr_zi0 zr_zz0 ([b0; b1] ++ rest) 0 zzero 0 cap) q'
                 ltac:(reflexivity)
                 ltac:(cbn [zrq q_st zr_zi0 s_hdr h_wrap]; lia) EN).
      reflexivity. }
    destruct (zr_dictid_absorb C0 q' HmD HdD)
      as [ (q2 & HL1 & Hq2) | (q2 & HL1) ].
    + (* out of input: leave with ret Z_OK *)
      pose proof (inf_loop_after_iter 1 C0 _ q' 1 _ HE1 HL1) as HC.
      pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
      cbv beta iota in Hrun.
      destruct (inf_leave C0 q2) as [q3 r] eqn:ELV.
      try rewrite ELV in Hrun; cbv beta iota in Hrun.
      assert (Hne : r <> Z_STREAM_END).
      { pose proof (zr_leave_ret_ne C0 q2) as HNE.
        rewrite ELV in HNE. cbn [snd] in HNE.
        apply HNE. rewrite Hq2, Hret'.
        unfold Z_OK, Z_STREAM_END. lia. }
      cbn [r_ret r_q] in Hrun.
      rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hrun.
      discriminate Hrun.
    + (* InfRet Z_NEED_DICT: the model returns 2, not STREAM_END *)
      pose proof (inf_loop_after_iter 1 C0 _ q' 1 _ HE1 HL1) as HC.
      pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
      cbv beta iota in Hrun.
      cbn [r_ret r_q] in Hrun.
      change (Z_NEED_DICT =? Z_STREAM_END) with false in Hrun.
      cbv beta iota in Hrun.
      discriminate Hrun.
  - (* PASS: M_TYPE at flags 0; the walk *)
    set (qe := zrq (zr_zist_t M_TYPE dm) z'
                   ([b0; b1] ++ rest) 2 zzero 0 cap) in EN, HE1.
    assert (HBW : br_wf (q_br qe)).
    { apply zr_zrq_brwf; [| exact HBy].
      rewrite zlen_app. change (zlen [b0; b1]) with 2.
      unfold zlen. lia. }
    assert (He : zr_body_entry qe).
    { unfold zr_body_entry.
      refine (conj HBW (conj _ (conj _ (conj _ (conj _ (conj _
                (conj _ (conj _ (conj _ (conj _ _)))))))))).
      - unfold qe, zrq. cbn [q_ob o_put]. lia.
      - unfold qe, zrq. cbn [q_ob o_left]. lia.
      - unfold qe, zrq. cbn [q_ob q_out o_put o_left]. lia.
      - unfold qe, zrq. cbn [q_out]. lia.
      - reflexivity.
      - unfold qe, zrq, zr_zist_t, zr_zi0. cbn [q_st s_tab t_sane]. lia.
      - reflexivity.
      - reflexivity.
      - apply zr_haligned_bits0. reflexivity.
      - unfold qe, zrq. cbn [q_br br_have br_bits].
        change (0 / 8) with 0. lia. }
    destruct (zr_body_walk_flags C0 qe HC0 He ltac:(reflexivity))
      as [ (k & q' & out & HI & HD & HS & Hwf' & Hop' & Hol' & Hsum & Hm'
            & Hl' & Hr' & Hin' & Hout' & Hwr' & Hfl' & Hck' & Hto' & Hws'
            & Hwh' & Hsn' & Hha' & Hbud')
         | [ (k & q' & HI & HB)
           | (n1 & s' & HL & HM) ] ].
    + (* AGREEMENT: the zlib tail at q' *)
      destruct (zr_zl_tail_len C0 q' HC0
                  ltac:(rewrite Hwr'; reflexivity)
                  ltac:(rewrite Hfl'; reflexivity)
                  Hwf' Hm' Hl')
        as [ (n2 & qx & HT & Hr2)
           | [ (n2 & qx & HT & Hr2)
             | (n2 & qx & HT & Hr2 & Hob2 & Hmd2 & Hwsz2 & Hslen) ] ].
      * (* ret preserved = Z_OK: not STREAM_END *)
        pose proof (zr_iterloop_compose k C0 qe q' n2 _ HI HT) as HC1.
        pose proof (inf_loop_after_iter 1 C0 _ qe _ _ HE1 HC1) as HC.
        pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
        cbv beta iota in Hrun.
        destruct (inf_leave C0 qx) as [q3 r] eqn:ELV.
        try rewrite ELV in Hrun; cbv beta iota in Hrun.
        assert (Hne : r <> Z_STREAM_END).
        { pose proof (zr_leave_ret_ne C0 qx) as HNE.
          rewrite ELV in HNE. cbn [snd] in HNE.
          apply HNE. rewrite Hr2, Hr'. vm_compute. lia. }
        cbn [r_ret r_q] in Hrun.
        rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hrun.
        discriminate Hrun.
      * (* DATA_ERROR: not STREAM_END *)
        pose proof (zr_iterloop_compose k C0 qe q' n2 _ HI HT) as HC1.
        pose proof (inf_loop_after_iter 1 C0 _ qe _ _ HE1 HC1) as HC.
        pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
        cbv beta iota in Hrun.
        destruct (inf_leave C0 qx) as [q3 r] eqn:ELV.
        try rewrite ELV in Hrun; cbv beta iota in Hrun.
        assert (Hne : r <> Z_STREAM_END).
        { pose proof (zr_leave_ret_ne C0 qx) as HNE.
          rewrite ELV in HNE. cbn [snd] in HNE.
          apply HNE. rewrite Hr2.
          unfold Z_DATA_ERROR, Z_STREAM_END. lia. }
        cbn [r_ret r_q] in Hrun.
        rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hrun.
        discriminate Hrun.
      * (* Z_STREAM_END: the success path *)
        pose proof (zr_iterloop_compose k C0 qe q' n2 _ HI HT) as HC1.
        pose proof (inf_loop_after_iter 1 C0 _ qe _ _ HE1 HC1) as HC.
        pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
        cbv beta iota in Hrun.
        destruct (inf_leave C0 qx) as [q3 r] eqn:ELV.
        try rewrite ELV in Hrun; cbv beta iota in Hrun.
        destruct (zr_leave_done_fin C0 qx ltac:(reflexivity) Hr2 Hmd2
                    ltac:(rewrite Hwsz2, Hws'; reflexivity))
          as (Hr3 & Hob3).
        rewrite ELV in Hr3, Hob3. cbn [fst snd] in Hr3, Hob3.
        rewrite Hr3 in Hrun.
        rewrite Z.eqb_refl in Hrun.
        cbn [r_ret r_q] in Hrun.
        injection Hrun as <-.
        rewrite Hob3, Hob2, HS.
        replace (ob_slice (q_ob qe) 0 (o_put (q_ob qe)))
          with (@nil Z) in HD by reflexivity.
        assert (HBS : br_stream (q_br qe) = bytes_bits rest).
        { unfold qe, zrq. cbn [q_br].
          replace (zlen ([b0; b1] ++ rest) - 2) with (zlen rest)
            by (rewrite zlen_app; change (zlen [b0; b1]) with 2; lia).
          replace 2 with (zlen [b0; b1]) by reflexivity.
          apply zr_br_stream_at. }
        rewrite HBS in HD.
        unfold rest in HD. rewrite bytes_bits_app in HD.
        apply (zr_dec_split _ _ _ _ HD).
        2:{ exists 4%nat. rewrite bytes_bits_length.
            unfold be32. cbn [length]. reflexivity. }
        rewrite bytes_bits_length.
        unfold be32. cbn [length].
        lia.
    + (* BAD out of the walk *)
      pose proof (zr_bad_absorb C0 q' HB) as HBA.
      pose proof (zr_iterloop_compose k C0 qe q' 1 _ HI HBA) as HC1.
      pose proof (inf_loop_after_iter 1 C0 _ qe _ _ HE1 HC1) as HC.
      pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
      cbv beta iota in Hrun.
      destruct (inf_leave C0 (qset_ret q' Z_DATA_ERROR)) as [q3 r] eqn:ELV.
      try rewrite ELV in Hrun; cbv beta iota in Hrun.
      assert (Hne : r <> Z_STREAM_END).
      { pose proof (zr_leave_ret_ne C0 (qset_ret q' Z_DATA_ERROR)) as HNE.
        rewrite ELV in HNE. cbn [snd] in HNE.
        apply HNE.
        cbn [q_ret qset_ret].
        unfold Z_DATA_ERROR, Z_STREAM_END. lia. }
      cbn [r_ret r_q] in Hrun.
      rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hrun.
      discriminate Hrun.
    + (* EXIT: leave with the entry ret, or fuel *)
      pose proof (inf_loop_after_iter 1 C0 _ qe _ _ HE1 HL) as HC.
      pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
      destruct s' as [q2|q2|q2 r0|m0|].
      * contradiction HM.
      * cbv beta iota in Hrun.
        destruct (inf_leave C0 q2) as [q3 r] eqn:ELV.
        try rewrite ELV in Hrun; cbv beta iota in Hrun.
        assert (Hne : r <> Z_STREAM_END).
        { pose proof (zr_leave_ret_ne C0 q2) as HNE.
          rewrite ELV in HNE. cbn [snd] in HNE.
          apply HNE.
          rewrite HM.
          vm_compute. lia. }
        cbn [r_ret r_q] in Hrun.
        rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hrun.
        discriminate Hrun.
      * contradiction HM.
      * contradiction HM.
      * cbv beta iota in Hrun.
        discriminate Hrun.
Qed.

End ZlibAsm.

(** THE composition: the three Section hypotheses discharged by the
    landed walk (ZReproQ6W.zr_body_walk_fuel — post-#10 [zr_body_exit]
    unfolds to exactly the inlined trichotomy), the landed tail
    (Q6ZlibTail.zr_zl_tail) and the landed split
    (Q6DecSplit.dec_stream_split).  The zlib face's remaining residue
    after this theorem = the two leg Props. *)
Theorem zr_zlib_core_final :
  ZrHuffFixedLeg -> ZrHuffDynLeg ->
  forall cap b0 b1 body ad y,
    0 <= cap ->
    cap <= 4294967295 ->
    zlen ([b0; b1] ++ body ++ be32 ad) <= 4294967290 ->
    Forall (fun b => 0 <= b < 256) ([b0; b1] ++ body ++ be32 ad) ->
    zr_inflate Z_FINISH 15 cap ([b0; b1] ++ body ++ be32 ad) = Some y ->
    dec_stream (bytes_bits body) = Some y.
Proof.
  intros HFix HDyn.
  apply zr_zlib_core_asm.
  - intros c q Hc He Hm.
    exact (zr_body_walk_fuel (S (length (br_stream (q_br q)))) c q
             HFix HDyn Hc ltac:(lia) He Hm).
  - exact zr_zl_tail.
  - exact dec_stream_split.
Qed.

Print Assumptions zr_zlib_core_final.
