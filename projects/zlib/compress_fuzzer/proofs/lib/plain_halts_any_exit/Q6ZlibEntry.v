(** * Q6ZlibEntry — the zlib header step: init at wb 15, one composite step.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; trilogy).
    Unlike gzip's concrete 10-byte header, the zlib header is TWO
    QUANTIFIED bytes (the face's core is header-validity-free), so the
    four header checks are DESTRUCTED rather than computed: each failure
    lands in M_BAD (absorbed), FDICT lands in M_DICTID (absorbed via
    Z_NEED_DICT — [zr_dictid_absorb]), and the pass lands at M_TYPE with
    flags 0, the adler-init check, and [dmax = 2^len] carried as an
    existential (len depends on b0's high nibble; nothing downstream
    reads dmax).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits BwStream ZBitsIn Inflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRepro ZReproL0C.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The wb-15 init state, explicit (= [ZReproL0C.zr_ist0], pinned by vm). *)
Definition zr_zi0 : IState :=
  {| s_hdr := {| h_mode := M_HEAD; h_last := 0; h_wrap := 5; h_havedict := 0;
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

Definition zr_zz0 : Strm :=
  {| z_tin := 0; z_tout := 0; z_adler := 1; z_dtype := 0; z_msg := 0 |}.

Lemma zr_init_15' :
  inflateInit2 z_fresh state_fresh 15 = Some (zr_zz0, zr_zi0).
Proof. vm_compute. reflexivity. Qed.

(** The post-HEAD zlib template: flags 0, adler-init check, dmax varies. *)
Definition zr_zist_t (m : Mode) (dm : Z) : IState :=
  {| s_hdr := {| h_mode := m; h_last := 0; h_wrap := 5; h_havedict := 0;
                 h_flags := 0; h_dmax := dm;
                 h_check := adler32_z 0 true [];
                 h_total := 0; h_head := 0 |};
     s_win := s_win zr_zi0; s_cur := s_cur zr_zi0; s_tab := s_tab zr_zi0;
     s_bld := s_bld zr_zi0; s_hold := 0; s_bits := 0 |}.

(* ==========================================================================
   1.  The two absorbers the non-pass arms hand to the assemblies.
   ========================================================================== *)

Lemma zr_bad_absorb : forall c q,
  h_mode (s_hdr (q_st q)) = M_BAD ->
  inf_loop 1 c q = Some (InfLeave (qset_ret q Z_DATA_ERROR)).
Proof.
  intros c q Hm. cbn [inf_loop].
  unfold inf_step, q_mode. rewrite Hm.
  unfold inf_BAD. reflexivity.
Qed.

Lemma zr_dictid_absorb : forall c q,
  h_mode (s_hdr (q_st q)) = M_DICTID ->
  h_havedict (s_hdr (q_st q)) = 0 ->
  (exists q2, inf_loop 1 c q = Some (InfLeave q2) /\ q_ret q2 = q_ret q)
  \/ (exists q2, inf_loop 1 c q = Some (InfRet q2 Z_NEED_DICT)).
Proof.
  intros c q Hm Hd. cbn [inf_loop].
  unfold inf_step, q_mode. rewrite Hm.
  unfold inf_DICTID.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:EN.
  - right. unfold inf_DICT.
    match goal with |- context [h_havedict (s_hdr (q_st ?X))] =>
      replace (h_havedict (s_hdr (q_st X)))
        with (h_havedict (s_hdr (q_st q))) by reflexivity end.
    rewrite Hd.
    change (0 =? 0) with true. cbv beta iota.
    eexists. reflexivity.
  - left. eexists. split; [reflexivity | reflexivity].
Qed.

(* ==========================================================================
   2.  THE entry step.
   ========================================================================== *)

Lemma zr_zl_entry : forall z b0 b1 rest obuf put cap,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  (exists q', inf_step zr_ic (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap)
              = InfCont q'
      /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists q', inf_step zr_ic (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap)
              = InfCont q'
      /\ h_mode (s_hdr (q_st q')) = M_DICTID
      /\ h_havedict (s_hdr (q_st q')) = 0)
  \/ (exists z' dm,
        inf_step zr_ic (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap)
        = InfCont (zrq (zr_zist_t M_TYPE dm) z'
                       ([b0; b1] ++ rest) 2 obuf put cap)).
Proof.
  intros z b0 b1 rest obuf put cap Hb0 Hb1.
  assert (Hr : 0 <= zlen rest) by (unfold zlen; lia).
  assert (Hlen : zlen ([b0; b1] ++ rest) = 2 + zlen rest).
  { rewrite zlen_app. unfold zlen. cbn [length]. lia. }
  unfold inf_step.
  replace (q_mode (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))
    with M_HEAD by reflexivity.
  cbv iota.
  unfold inf_HEAD. cbv zeta.
  replace (h_wrap (s_hdr (q_st (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))))
    with 5 by reflexivity.
  change (5 =? 0) with false. cbv beta iota.
  match goal with |- context [inf_nb 16 ?br] =>
    replace br with {| br_in := zlist ([b0; b1] ++ rest);
                       br_have := zlen ([b0; b1] ++ rest) - 0;
                       br_next := 0; br_hold := 0; br_bits := 0 |}
      by reflexivity end.
  rewrite inf_nb_pull2 by lia.
  replace (zlist ([b0; b1] ++ rest) 0) with b0 by reflexivity.
  replace (zlist ([b0; b1] ++ rest) (0 + 1)) with b1 by reflexivity.
  cbn [br_hold br_bits br_in br_next br_have].
  replace (Z.land 5 2) with 0 by reflexivity.
  change (0 =? 0) with true. cbn [negb andb].
  replace (Z.land 5 1) with 1 by reflexivity.
  change (1 =? 0) with false. cbn [orb].
  match goal with |- context [if negb (?T =? 0) then _ else _] =>
    destruct (Z.eqb_spec T 0) as [EF|EF] end.
  2:{ cbn [negb]. left. eexists. split; [reflexivity | reflexivity]. }
  cbn [negb].
  match goal with |- context [if negb (?C =? Z_DEFLATED) then _ else _] =>
    destruct (Z.eqb_spec C Z_DEFLATED) as [EC|EC] end.
  2:{ cbn [negb]. left. eexists. split; [reflexivity | reflexivity]. }
  cbn [negb]. cbv zeta.
  replace (w_wbits (s_win (q_st (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))))
    with 15 by reflexivity.
  change (15 =? 0) with false. cbv beta iota.
  match goal with |- context [if ?T1 || ?T2 then _ else _] =>
    destruct (T1 || T2) eqn:EW end.
  { left. eexists. split; [reflexivity | reflexivity]. }
  match goal with |- context [if Z.land ?H 512 =? 0 then M_TYPE else M_DICTID] =>
    destruct (Z.eqb_spec (Z.land H 512) 0) as [ED|ED] end.
  - (* M_TYPE: the pass arm *)
    right; right. do 2 eexists.
    f_equal.
    lazy [qmode qcheck qset_br qset_st qset_z set_mode set_flags
          set_dmax set_wbits br_initbits zrq zr_zist_t zr_zi0
          q_st q_z q_br q_ob q_in q_out q_ret
          br_in br_have br_next br_hold br_bits
          s_hdr s_win s_cur s_tab s_bld s_hold s_bits
          h_mode h_last h_wrap h_havedict h_flags h_dmax h_check h_total
          h_head].
    f_equal; first [reflexivity | lia | f_equal; first [reflexivity | lia]].
  - (* M_DICTID: FDICT set *)
    right; left. eexists. split; [reflexivity|].
    split; reflexivity.
Qed.

Print Assumptions zr_zl_entry.
Print Assumptions zr_bad_absorb.
Print Assumptions zr_dictid_absorb.
