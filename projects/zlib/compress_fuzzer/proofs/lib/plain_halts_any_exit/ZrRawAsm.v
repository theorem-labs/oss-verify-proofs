(** * ZrRawAsm — THE raw face assembly: init + body walk + tail = ZrRawCore.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20).
    Section-hypothesized on model-rt's body walk (head0 entry);
    everything else is landed: Q6AsmSupport's loop/leave/init lemmas,
    Q6RawTail's composed tail, Q6ZlibEntry's zr_bad_absorb.  The footer
    discharges the hypothesis with model-rt's landed walk, so the raw
    face's remaining residue is exactly the two leg Props.

    v2 (amendment #10, three-way frozen text +
    q7 fit-check CONFIRMED + model-rt GO): the walk hypothesis gains the
    reader-alignment and compositional-budget premises after br_wf, the
    agreement arm gains the flags clause after h_wrap and returns
    haligned+budget appended LAST; the entry discharges are vacuous at
    the fresh reader (bits = 0: Q6AsmSupport.zr_haligned_bits0 /
    zr_init_budget — the budget collapses to the face's zlen premise,
    which is why this statement has carried it since v1).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits BwStream ZBitsIn Huff DeflateSpec
  InflateFast Inflate Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproQ6A ZReproL0C ZReproL0E Q6AsmSupport Q6RawTail Q6ZlibEntry
  Q6HuffResidue ZReproQ6W.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The raw (wb -15) init pair, explicit (pinned by vm). *)
Definition zr_rz0 : Strm :=
  {| z_tin := 0; z_tout := 0; z_adler := 0; z_dtype := 0; z_msg := 0 |}.

Definition zr_ri0 : IState :=
  {| s_hdr := {| h_mode := M_HEAD; h_last := 0; h_wrap := 0; h_havedict := 0;
                 h_flags := -1; h_dmax := 32768; h_check := 0;
                 h_total := 0; h_head := 0 |};
     s_win := {| w_wbits := 15; w_wsize := 0; w_whave := 0; w_wnext := 0;
                 w_alloc := false; w_win := zzero |};
     s_cur := {| u_length := 0; u_offset := 0; u_extra := 0;
                 u_back := -1; u_was := 0 |};
     s_tab := {| t_lencode := TRcodes 0; t_distcode := TRcodes 0;
                 t_lenbits := 0; t_distbits := 0; t_next := 0;
                 t_codes := tnone; t_sane := 1 |};
     s_bld := {| b_ncode := 0; b_nlen := 0; b_ndist := 0; b_have := 0;
                 b_lens := zzero; b_work := zzero |};
     s_hold := 0; s_bits := 0 |}.

Lemma zr_init_m15 :
  inflateInit2 z_fresh state_fresh (-15) = Some (zr_rz0, zr_ri0).
Proof. vm_compute. reflexivity. Qed.

Section RawAsm.

(** model-rt's body walk at the wrap-0 M_HEAD entry — the #10-amended
    statement; discharged by their landed theorem at composition time. *)
Hypothesis zr_body_walk_head0 : forall c q,
  zr_cflush_ok c ->
  br_wf (q_br q) ->
  W2Stream.br_haligned (q_br q) ->
  br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  q_ret q = 0 ->
  h_last (s_hdr (q_st q)) = 0 ->
  h_mode (s_hdr (q_st q)) = M_HEAD ->
  h_wrap (s_hdr (q_st q)) = 0 ->
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
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
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

Theorem zr_raw_core_asm : forall cap enc y,
  0 <= cap ->
  cap <= 4294967295 ->
  zlen enc <= 4294967290 ->
  Forall (fun b => 0 <= b < 256) enc ->
  zr_inflate Z_FINISH (-15) cap enc = Some y ->
  dec_stream (bytes_bits enc) = Some y.
Proof.
  intros cap enc y Hc0 Hcap Henc HBy.
  unfold zr_inflate.
  rewrite zr_init_m15.
  unfold zr_inf_call, inflate_model.
  cbv beta iota zeta.
  cbn [g_state_null g_out_null g_in_null g_st g_z g_inbuf g_next_in
       g_avail_in g_outbuf g_next_out g_avail_out g_flush g_walloc
       g_wfresh orb andb negb].
  set (Q0 := inf_st0 _).
  match goal with |- context [inf_loop _ ?C _] => set (C0 := C) end.
  assert (HC0 : zr_cflush_ok C0).
  { unfold zr_cflush_ok, C0, inf_ctx. cbn [n_flush g_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  match goal with |- context [inf_loop ?F ?C ?Q] =>
    destruct (inf_loop F C Q) as [s|] eqn:ELOOP
  end;
  cbv beta iota;
  [ intro Hrun | discriminate ].
  (* the walk at Q0 *)
  destruct (zr_body_walk_head0 C0 Q0
              HC0
              (zr_init_brwf enc HBy)
              ltac:(apply zr_haligned_bits0; reflexivity)
              ltac:(exact (zr_init_budget enc Henc))
              ltac:(unfold Q0; cbn; lia)
              ltac:(exact Hc0)
              ltac:(reflexivity)
              ltac:(exact Hcap)
              ltac:(reflexivity)
              ltac:(unfold Q0; cbn; lia)
              ltac:(reflexivity)
              ltac:(reflexivity)
              ltac:(reflexivity)
              ltac:(reflexivity))
    as [ (k & q' & out & HI & HD & HS & Hwf' & Hop' & Hol' & Hsum & Hm'
          & Hl' & Hr' & Hin' & Hout' & Hwr' & Hfl' & Hck' & Hto' & Hws'
          & Hwh' & Hsn' & Hha' & Hbud')
       | [ (k & q' & HI & HB)
         | (n & s' & HL & HM) ] ].
  - (* AGREEMENT: block walk done; run the raw tail *)
    destruct (zr_raw_tail C0 q'
                HC0
                ltac:(rewrite Hwr'; reflexivity)
                Hm' Hl')
      as (q2 & HT & Hret2 & Hob2 & Hmd2 & Hwsz2).
    pose proof (zr_iterloop_compose k C0 Q0 q' 2 _ HI HT) as HC.
    pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HC) as ->.
    cbv beta iota in Hrun.
    destruct (inf_leave C0 q2) as [q3 r] eqn:ELV.
    try rewrite ELV in Hrun; cbv beta iota in Hrun.
    destruct (zr_leave_done_fin C0 q2 ltac:(reflexivity) Hret2 Hmd2
                ltac:(rewrite Hwsz2, Hws'; reflexivity))
      as (Hr3 & Hob3).
    rewrite ELV in Hr3, Hob3. cbn [fst snd] in Hr3, Hob3.
    rewrite Hr3 in Hrun.
    rewrite Z.eqb_refl in Hrun.
    injection Hrun as <-.
    replace (br_stream (q_br Q0)) with (bytes_bits enc) in HD
      by (symmetry; exact (zr_br_stream_at [] enc 0)).
    replace (ob_slice (q_ob Q0) 0 (o_put (q_ob Q0))) with (@nil Z) in HD
      by reflexivity.
    unfold dec_stream, dec_stream_rem.
    rewrite HD.
    cbn [option_map fst].
    f_equal.
    rewrite Hob3, Hob2. symmetry. exact HS.
  - (* BAD: one more step to the DATA_ERROR leave *)
    pose proof (zr_bad_absorb C0 q' HB) as HBA.
    pose proof (zr_iterloop_compose k C0 Q0 q' 1 _ HI HBA) as HC.
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
    destruct s' as [q2|q2|q2 r0|m0|].
    + contradiction HM.
    + (* InfLeave, ret preserved = Z_OK *)
      pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HL) as ->.
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
      pose proof (zr_loop_uniq _ _ _ _ _ _ ELOOP HL) as ->.
      cbv beta iota in Hrun.
      discriminate Hrun.
Qed.


End RawAsm.

(** THE composition: the Section hypothesis discharged by model-rt's
    landed walk (ZReproQ6W.zr_body_walk_head0), premises re-plumbed from
    my flat spelling into their zr_body_entry bundle (#10: haligned +
    budget appended last).  The raw face's remaining residue after this
    theorem = the two leg Props. *)
Theorem zr_raw_core_final :
  ZrHuffFixedLeg -> ZrHuffDynLeg ->
  forall cap enc y,
    0 <= cap ->
    cap <= 4294967295 ->
    zlen enc <= 4294967290 ->
    Forall (fun b => 0 <= b < 256) enc ->
    zr_inflate Z_FINISH (-15) cap enc = Some y ->
    dec_stream (bytes_bits enc) = Some y.
Proof.
  intros HFix HDyn.
  apply zr_raw_core_asm.
  intros c q Hc Hwf Hha Hbud Hput Hleft Htie Hcap Hwh Hsn Hrt Hlast Hm Hw.
  exact (zr_body_walk_head0 c q HFix HDyn Hc
           (conj Hwf (conj Hput (conj Hleft (conj Htie (conj Hcap
              (conj Hwh (conj Hsn (conj Hrt (conj Hlast
                 (conj Hha Hbud))))))))))
           Hm Hw).
Qed.

Print Assumptions zr_raw_core_final.
