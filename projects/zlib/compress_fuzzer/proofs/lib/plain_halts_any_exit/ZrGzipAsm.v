(** * ZrGzipAsm — gzip face assembly: init + entry + body walk + tail.

    OWNER: q6-asm-copier (q6-fixedtbl lane, zlib z-repro campaign,
    2026-08-20).  Shape copied from the GREEN ZrRawAsm.v.

    STATEMENT-TIME GAPS (three Section Hypotheses, each the exact clause
    a landed statement is missing — this file machine-checks their
    SUFFICIENCY; nothing else is hypothesized):

    1. [zr_body_walk_flags] — the landed [ZReproQ6W.zr_body_exit]
       agreement arm does NOT export h_flags preservation (it carries
       ret/in/out/wrap/wsize/whave/sane only; ZReproQ6W.v:481-508), but
       [Q6GzipTail.zr_gz_tail] REQUIRES [h_flags = 8] at the walk-exit
       state (Q6GzipTail.v:83).  No body arm writes flags ([set_flags]
       sites: Inflate.v:1682 inf_FLAGS, :1735 inf_HEAD, :1944
       inflateResetKeep — all header/reset, none in the body loop), so
       the amendment is TRUE; it must be added to the walk's exit bundle.
    2. [zr_gz_tail_len] — zr_gz_tail's Z_STREAM_END arm does not export
       any stream fact at its ENTRY state, but the dec-split below needs
       [64 <= length (br_stream (q_br q))] (the 8 trailer bytes the CHECK
       + LENGTH arms actually consumed on that arm).
    3. [zr_dec_split] — the suffix-invariance split for
       [dec_stream_from]: no reverse-direction lemma exists in the tree
       (all landed ++-lemmas are encoder-direction), and it is NOT a
       <100-line induction (needs per-primitive locality through
       read_bits/decode_stored/decode_symbols/decode_dynamic_tables).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits BwStream ZBitsIn Huff DeflateSpec
  InflateFast Inflate Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproQ6A ZReproL0C ZReproL0E ZReproQ6I Q6AsmSupport
  Q6GzipEntry Q6GzipTail Q6ZlibEntry Q6HuffResidue ZReproQ6W Q6DecSplit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Plumbing: the model's init state IS the zrq packaging.
   ========================================================================== *)

Lemma zr_gz_q0 : forall enc cap,
  inf_st0 {| g_st := zr_gist M_HEAD 0 (-1) 0 0; g_state_null := false;
             g_z := zr_gz0; g_inbuf := zlist enc; g_next_in := 0;
             g_avail_in := zlen enc; g_in_null := false;
             g_outbuf := zzero; g_next_out := 0; g_avail_out := cap;
             g_out_null := false; g_flush := Z_FINISH; g_walloc := true;
             g_wfresh := zzero |}
  = zrq (zr_gist M_HEAD 0 (-1) 0 0) zr_gz0 enc 0 zzero 0 cap.
Proof.
  intros enc cap.
  unfold inf_st0, zrq.
  cbn [g_st g_z g_inbuf g_next_in g_avail_in g_outbuf g_next_out
       g_avail_out zr_gist s_hdr h_mode s_hold s_bits].
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

Section GzipAsm.

(** GAP 1 — the walk with the flags clause (line marked THE GAP) added
    to the agreement arm of [zr_body_exit]; legs re-plumbed at discharge
    time exactly as ZrRawAsm's footer does. *)
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
     /\ W2Stream.br_haligned (q_br q')
     /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290)
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

(** GAP 2 — zr_gz_tail with the stream-length export (marked) added to
    the Z_STREAM_END arm. *)
Hypothesis zr_gz_tail_len : forall c q,
  zr_cflush_ok c ->
  h_wrap (s_hdr (q_st q)) = 6 ->
  h_flags (s_hdr (q_st q)) = 8 ->
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
     /\ (64 <= length (br_stream (q_br q)))%nat).            (* THE GAP *)

(** GAP 3 — the dec-side suffix-invariance split (consumer form). *)
Hypothesis zr_dec_split : forall bits1 bits2 out rem,
  dec_stream_from (bits1 ++ bits2) [] = Some (out, rem) ->
  (length bits2 <= length rem)%nat ->
  (exists k, length bits2 = (8 * k)%nat) ->
  dec_stream bits1 = Some out.

Theorem zr_gzip_core_asm : forall cap body tc tn y,
  0 <= cap ->
  cap <= 4294967295 ->
  zlen (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn)
    <= 4294967290 ->
  Forall (fun b => 0 <= b < 256)
    (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn) ->
  zr_inflate Z_FINISH 31 cap
    (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn) = Some y ->
  dec_stream (bytes_bits body) = Some y.
Proof.
  intros cap body tc tn y Hc0 Hcap Henc HBy.
  set (rest := body ++ zr_le32 tc ++ zr_le32 tn) in *.
  unfold zr_inflate.
  rewrite zr_init_31.
  unfold zr_inf_call, inflate_model.
  cbv beta iota zeta.
  cbn [g_state_null g_out_null g_in_null g_st g_z g_inbuf g_next_in
       g_avail_in g_outbuf g_next_out g_avail_out g_flush g_walloc
       g_wfresh orb andb negb].
  rewrite zr_gz_q0.
  match goal with |- context [inf_loop _ ?C _] => set (C0 := C) end.
  assert (HC0 : zr_cflush_ok C0).
  { unfold zr_cflush_ok, C0, inf_ctx. cbn [n_flush g_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  match goal with |- context [inf_loop ?F ?C ?Q] =>
    destruct (inf_loop F C Q) as [s|] eqn:ELOOP
  end;
  cbv beta iota;
  [ intro Hrun | discriminate ].
  (* the header entry, at the loop's ctx *)
  destruct (zr_gz_entry zr_gz0 rest zzero 0 cap) as [z2 HE].
  change zr_ic with C0 in HE.
  set (qe := zrq (zr_gist M_TYPE 0 8 (crc32_z 0 true 0 []) 0) z2
                 (zr_gzip_header 9 ++ rest) 10 zzero 0 cap) in HE.
  (* the walk-entry bundle at qe *)
  assert (HBW : br_wf (q_br qe)).
  { apply zr_zrq_brwf; [| exact HBy].
    rewrite zlen_app, zr_gz_hdr_len. unfold zlen. lia. }
  assert (He : zr_body_entry qe).
  { unfold zr_body_entry.
    refine (conj HBW (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ (conj _ (conj _ _)))))))))).
    - unfold qe, zrq. cbn [q_ob o_put]. lia.
    - unfold qe, zrq. cbn [q_ob o_left]. lia.
    - unfold qe, zrq. cbn [q_ob q_out o_put o_left]. lia.
    - unfold qe, zrq. cbn [q_out]. lia.
    - reflexivity.
    - unfold qe, zrq, zr_gist. cbn [q_st s_tab t_sane]. lia.
    - reflexivity.
    - reflexivity.
    - apply zr_haligned_bits0. reflexivity.
    - unfold qe, zrq. cbn [q_br br_have br_bits].
      change (0 / 8) with 0. lia. }
  (* the walk at qe *)
  destruct (zr_body_walk_flags C0 qe HC0 He ltac:(reflexivity))
    as [ (k & q' & out & HI & HD & HS & Hwf' & Hop' & Hol' & Hsum & Hm'
          & Hl' & Hr' & Hin' & Hout' & Hwr' & Hfl' & Hck' & Hto' & Hws'
          & Hwh' & Hsn' & Hha' & Hbud')
       | [ (k & q' & HI & HB)
         | (n1 & s' & HL & HM) ] ].
  - (* AGREEMENT: the gzip tail at q' *)
    destruct (zr_gz_tail_len C0 q' HC0
                ltac:(rewrite Hwr'; reflexivity)
                ltac:(rewrite Hfl'; reflexivity)
                Hwf' Hm' Hl')
      as [ (n2 & qx & HT & Hr2)
         | [ (n2 & qx & HT & Hr2)
           | (n2 & qx & HT & Hr2 & Hob2 & Hmd2 & Hwsz2 & Hslen) ] ].
    + (* ret preserved = Z_OK: not STREAM_END *)
      pose proof (zr_iterloop_compose k C0 qe q' n2 _ HI HT) as HC1.
      pose proof (inf_loop_after_iter 2 C0 _ qe _ _ HE HC1) as HC.
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
    + (* DATA_ERROR: not STREAM_END *)
      pose proof (zr_iterloop_compose k C0 qe q' n2 _ HI HT) as HC1.
      pose proof (inf_loop_after_iter 2 C0 _ qe _ _ HE HC1) as HC.
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
    + (* Z_STREAM_END: the success path *)
      pose proof (zr_iterloop_compose k C0 qe q' n2 _ HI HT) as HC1.
      pose proof (inf_loop_after_iter 2 C0 _ qe _ _ HE HC1) as HC.
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
      (* the dec split: HD is over bytes_bits (body ++ trailer) *)
      replace (ob_slice (q_ob qe) 0 (o_put (q_ob qe)))
        with (@nil Z) in HD by reflexivity.
      assert (HBS : br_stream (q_br qe) = bytes_bits rest).
      { unfold qe, zrq. cbn [q_br].
        replace (zlen (zr_gzip_header 9 ++ rest) - 10) with (zlen rest)
          by (rewrite zlen_app, zr_gz_hdr_len; lia).
        replace 10 with (zlen (zr_gzip_header 9))
          by (apply zr_gz_hdr_len).
        apply zr_br_stream_at. }
      rewrite HBS in HD.
      unfold rest in HD. rewrite bytes_bits_app in HD.
      apply (zr_dec_split _ _ _ _ HD).
      { rewrite bytes_bits_length, length_app.
        unfold zr_le32. cbn [length].
        lia. }
      exists (length (zr_le32 tc ++ zr_le32 tn)).
      apply bytes_bits_length.
  - (* BAD: one more step to the DATA_ERROR leave *)
    pose proof (zr_bad_absorb C0 q' HB) as HBA.
    pose proof (zr_iterloop_compose k C0 qe q' 1 _ HI HBA) as HC1.
    pose proof (inf_loop_after_iter 2 C0 _ qe _ _ HE HC1) as HC.
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
  - (* EXIT: leave with the entry ret, or fuel *)
    pose proof (inf_loop_after_iter 2 C0 _ qe _ _ HE HL) as HC.
    pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
    destruct s' as [q2|q2|q2 r0|m0|].
    + contradiction HM.
    + (* InfLeave, ret preserved = Z_OK *)
      cbv beta iota in Hrun.
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
    + contradiction HM.
    + contradiction HM.
    + (* InfFuel *)
      cbv beta iota in Hrun.
      discriminate Hrun.
Qed.

End GzipAsm.

Print Assumptions zr_gzip_core_asm.

(** THE composition: the three Section hypotheses discharged by the
    landed walk (ZReproQ6W.zr_body_walk_fuel), tail
    (Q6GzipTail.zr_gz_tail) and split (Q6DecSplit.dec_stream_split).
    The gzip face's remaining residue after this theorem = the two leg
    Props. *)
Theorem zr_gzip_core_final :
  ZrHuffFixedLeg -> ZrHuffDynLeg ->
  forall cap body tc tn y,
    0 <= cap ->
    cap <= 4294967295 ->
    zlen (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn)
      <= 4294967290 ->
    Forall (fun b => 0 <= b < 256)
      (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn) ->
    zr_inflate Z_FINISH 31 cap
      (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn) = Some y ->
    dec_stream (bytes_bits body) = Some y.
Proof.
  intros HFix HDyn.
  apply zr_gzip_core_asm.
  - intros c q Hc He Hm.
    exact (zr_body_walk_fuel (S (length (br_stream (q_br q)))) c q
             HFix HDyn Hc ltac:(lia) He Hm).
  - exact zr_gz_tail.
  - exact dec_stream_split.
Qed.

Print Assumptions zr_gzip_core_final.
