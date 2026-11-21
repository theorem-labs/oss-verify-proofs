(** * Q6GzipEntry — the gzip header walk: init at wb 31 to M_TYPE in 2 steps.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20).  At the
    harness frame ([ZR_FramedGzip 9]) the FLG byte is 0, so every
    optional header arm (EXLEN/EXTRA/NAME/COMMENT/HCRC) takes its
    flag-off fall-through and the header is TWO composite steps: HEAD
    reads the 2 magic bytes; FLAGS chains TIME/OS and the five skips to
    M_TYPE, reading CM+FLG (16), MTIME (32), XFL+OS (16).  Ten bytes
    consumed exactly.  Proof idiom is ZReproL0C's (zrq packaging, pull
    lemmas for NEEDBITS, closed atoms by replace-with-reflexivity).

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

(** The walk's gzip [IState]: closed except mode, BFINAL, flags, check,
    and the length counter (the tail leg reuses the template). *)
Definition zr_gist (m : Mode) (last flags check len : Z) : IState :=
  {| s_hdr := {| h_mode := m; h_last := last; h_wrap := 6; h_havedict := 0;
                 h_flags := flags; h_dmax := 32768; h_check := check;
                 h_total := 0; h_head := 0 |};
     s_win := {| w_wbits := 15; w_wsize := 0; w_whave := 0; w_wnext := 0;
                 w_alloc := false; w_win := zzero |};
     s_cur := {| u_length := len; u_offset := 0; u_extra := 0;
                 u_back := -1; u_was := 0 |};
     s_tab := {| t_lencode := TRcodes 0; t_distcode := TRcodes 0;
                 t_lenbits := 0; t_distbits := 0; t_next := 0;
                 t_codes := tnone; t_sane := 1 |};
     s_bld := {| b_ncode := 0; b_nlen := 0; b_ndist := 0; b_have := 0;
                 b_lens := zzero; b_work := zzero |};
     s_hold := 0; s_bits := 0 |}.

(** Init at 31 IS the template at M_HEAD (flags -1, per inflateReset). *)
Definition zr_gz0 : Strm :=
  {| z_tin := 0; z_tout := 0; z_adler := 0; z_dtype := 0; z_msg := 0 |}.

Lemma zr_init_31 :
  inflateInit2 z_fresh state_fresh 31 = Some (zr_gz0, zr_gist M_HEAD 0 (-1) 0 0).
Proof. vm_compute. reflexivity. Qed.

(** The magic-arm header CRC over the two magic bytes — closed. *)
Definition zr_gz_ck2 : Z := crc32_z (crc32_z 0 true 0 []) false 0 [31; 139].

(** The concrete header. *)
Lemma zr_gz_hdr_bytes : zr_gzip_header 9 = [31;139;8;0;0;0;0;0;2;3].
Proof. vm_compute. reflexivity. Qed.

Lemma zr_gz_hdr_len : zlen (zr_gzip_header 9) = 10.
Proof. vm_compute. reflexivity. Qed.

(** Header-region reads, pinned to their values in the goal's spelling. *)
Lemma zr_gz_byte : forall rest k v,
  0 <= k < 10 ->
  zlist (zr_gzip_header 9) k = v ->
  zlist (zr_gzip_header 9 ++ rest) k = v.
Proof.
  intros rest k v Hk Hv. unfold zlist in *.
  rewrite app_nth1; [exact Hv|].
  rewrite zr_gz_hdr_bytes. cbn [length]. lia.
Qed.

(** ---- step 1: HEAD takes the gzip-magic branch, 2 bytes. ---- *)
Lemma zr_gz_step_head : forall z rest obuf put cap, exists z',
  inf_step zr_ic (zrq (zr_gist M_HEAD 0 (-1) 0 0) z
                      (zr_gzip_header 9 ++ rest) 0 obuf put cap)
  = InfCont (zrq (zr_gist M_FLAGS 0 (-1) zr_gz_ck2 0) z'
                 (zr_gzip_header 9 ++ rest) 2 obuf put cap).
Proof.
  intros z rest obuf put cap.
  assert (Hr : 0 <= zlen rest) by (unfold zlen; lia).
  pose proof zr_gz_hdr_len as HL.
  assert (Hlen : zlen (zr_gzip_header 9 ++ rest) = 10 + zlen rest)
    by (rewrite zlen_app, HL; reflexivity).
  eexists.
  unfold inf_step.
  replace (q_mode (zrq (zr_gist M_HEAD 0 (-1) 0 0) z
                       (zr_gzip_header 9 ++ rest) 0 obuf put cap))
    with M_HEAD by reflexivity.
  unfold inf_HEAD. cbv zeta.
  unfold zrq. cbn [q_st q_br].
  replace (h_wrap (s_hdr (zr_gist M_HEAD 0 (-1) 0 0))) with 6 by reflexivity.
  replace (6 =? 0) with false by reflexivity.
  rewrite inf_nb_pull2 by lia.
  rewrite (zr_gz_byte rest 0 31 ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (zr_gz_byte rest (0 + 1) 139 ltac:(lia) ltac:(vm_compute; reflexivity)).
  cbn [br_hold br_bits br_in br_next br_have].
  replace (Z.shiftl 31 0 + Z.shiftl 139 8) with 35615 by reflexivity.
  replace (Z.land 6 2) with 2 by reflexivity.
  replace (2 =? 0) with false by reflexivity.
  replace (35615 =? 35615) with true by reflexivity.
  cbn [negb andb].
  replace (w_wbits (s_win (zr_gist M_HEAD 0 (-1) 0 0))) with 15 by reflexivity.
  replace (15 =? 0) with false by reflexivity.
  replace (Z.land 35615 255) with 31 by reflexivity.
  replace (Z.land (Z.shiftr 35615 8) 255) with 139 by reflexivity.
  unfold qmode, qset_br, qset_st, set_check, set_mode, br_initbits.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits
       s_hdr s_win s_cur s_tab s_bld s_hold s_bits
       h_mode h_last h_wrap h_havedict h_flags h_dmax h_check h_total h_head].
  f_equal.
Qed.

(** ---- step 2, factored per arm (the monolithic unfold of all five
    skip arms makes every subsequent tactic traverse the whole term —
    each lemma below keeps the NEXT arm's application opaque, so the
    conversions stay small). ---- *)

(** The five flag-off skips, zrq-packaged on BOTH sides — the abstract
    setter-nest form duplicates the state ~7x per layer through the
    projections (the R18 duplication class; measured as a 50 GB OOM), so
    each skip normalizes its one layer here, where the record is small. *)
Lemma zr_gz_exlen_skip : forall ck z stream n obuf put cap,
  inf_EXLEN (zrq (zr_gist M_EXLEN 0 8 ck 0) z stream n obuf put cap)
  = inf_EXTRA (zrq (zr_gist M_EXTRA 0 8 ck 0) z stream n obuf put cap).
Proof.
  intros. unfold inf_EXLEN. cbn [zrq q_st zr_gist s_hdr h_flags].
  replace (Z.land 8 1024) with 0 by reflexivity.
  cbn [Z.eqb negb]. f_equal.
Qed.

Lemma zr_gz_extra_skip : forall ck z stream n obuf put cap,
  inf_EXTRA (zrq (zr_gist M_EXTRA 0 8 ck 0) z stream n obuf put cap)
  = inf_NAME (zrq (zr_gist M_NAME 0 8 ck 0) z stream n obuf put cap).
Proof.
  intros. unfold inf_EXTRA. cbv zeta.
  cbn [zrq q_st zr_gist s_hdr h_flags].
  replace (Z.land 8 1024) with 0 by reflexivity.
  cbn [Z.eqb negb]. f_equal.
Qed.

Lemma zr_gz_name_skip : forall ck z stream n obuf put cap,
  inf_NAME (zrq (zr_gist M_NAME 0 8 ck 0) z stream n obuf put cap)
  = inf_COMMENT (zrq (zr_gist M_COMMENT 0 8 ck 0) z stream n obuf put cap).
Proof.
  intros. unfold inf_NAME. cbn [zrq q_st zr_gist s_hdr h_flags].
  replace (Z.land 8 2048) with 0 by reflexivity.
  cbn [Z.eqb negb]. f_equal.
Qed.

Lemma zr_gz_comment_skip : forall ck z stream n obuf put cap,
  inf_COMMENT (zrq (zr_gist M_COMMENT 0 8 ck 0) z stream n obuf put cap)
  = inf_HCRC (zrq (zr_gist M_HCRC 0 8 ck 0) z stream n obuf put cap).
Proof.
  intros. unfold inf_COMMENT. cbn [zrq q_st zr_gist s_hdr h_flags].
  replace (Z.land 8 4096) with 0 by reflexivity.
  cbn [Z.eqb negb]. f_equal.
Qed.

Lemma zr_gz_hcrc_skip : forall ck z stream n obuf put cap,
  inf_HCRC (zrq (zr_gist M_HCRC 0 8 ck 0) z stream n obuf put cap)
  = InfCont (zrq (zr_gist M_TYPE 0 8 (crc32_z 0 true 0 []) 0)
                 (zset_adler z (crc32_z 0 true 0 []))
                 stream n obuf put cap).
Proof.
  intros. unfold inf_HCRC. cbn [zrq q_st zr_gist s_hdr h_flags].
  replace (Z.land 8 512) with 0 by reflexivity.
  cbn [Z.eqb negb]. f_equal.
Qed.

(** The three reading arms, zrq-packaged, next arm kept OPAQUE. *)
Lemma zr_gz_flags_arm : forall z rest obuf put cap,
  inf_FLAGS (zrq (zr_gist M_FLAGS 0 (-1) zr_gz_ck2 0) z
                 (zr_gzip_header 9 ++ rest) 2 obuf put cap)
  = inf_TIME (zrq (zr_gist M_TIME 0 8 zr_gz_ck2 0) z
                  (zr_gzip_header 9 ++ rest) 4 obuf put cap).
Proof.
  intros z rest obuf put cap.
  assert (Hr : 0 <= zlen rest) by (unfold zlen; lia).
  assert (Hlen : zlen (zr_gzip_header 9 ++ rest) = 10 + zlen rest)
    by (rewrite zlen_app, zr_gz_hdr_len; reflexivity).
  unfold inf_FLAGS.
  unfold zrq at 1. cbn [q_st q_br].
  rewrite inf_nb_pull2 by lia.
  rewrite (zr_gz_byte rest 2 8 ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (zr_gz_byte rest (2 + 1) 0 ltac:(lia) ltac:(vm_compute; reflexivity)).
  cbn [br_hold br_bits br_in br_next br_have].
  replace (Z.shiftl 8 0 + Z.shiftl 0 8) with 8 by reflexivity.
  unfold set_flags. cbn [q_st s_hdr h_flags h_mode h_last h_wrap h_havedict
                         h_dmax h_check h_total h_head zr_gist].
  replace (Z.land 8 255) with 8 by reflexivity.
  replace (8 =? Z_DEFLATED) with true by reflexivity.
  replace (Z.land 8 57344) with 0 by reflexivity.
  replace (Z.land 8 512) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  cbn [negb andb].
  f_equal.
  unfold qmode, qset_br, qset_st, set_mode, set_flags, br_initbits, zrq, zr_gist.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits
       s_hdr s_win s_cur s_tab s_bld s_hold s_bits
       h_mode h_last h_wrap h_havedict h_flags h_dmax h_check h_total h_head].
  f_equal; first [reflexivity | lia | f_equal; first [reflexivity | lia]].
Qed.

Lemma zr_gz_time_arm : forall z rest obuf put cap,
  inf_TIME (zrq (zr_gist M_TIME 0 8 zr_gz_ck2 0) z
                (zr_gzip_header 9 ++ rest) 4 obuf put cap)
  = inf_OS (zrq (zr_gist M_OS 0 8 zr_gz_ck2 0) z
                (zr_gzip_header 9 ++ rest) 8 obuf put cap).
Proof.
  intros z rest obuf put cap.
  assert (Hr : 0 <= zlen rest) by (unfold zlen; lia).
  assert (Hlen : zlen (zr_gzip_header 9 ++ rest) = 10 + zlen rest)
    by (rewrite zlen_app, zr_gz_hdr_len; reflexivity).
  unfold inf_TIME.
  unfold zrq at 1. cbn [q_st q_br].
  rewrite inf_nb_pull4 by lia.
  cbn [s_hdr h_flags zr_gist].
  replace (Z.land 8 512) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  cbn [negb andb].
  f_equal.
  unfold qmode, qset_br, qset_st, set_mode, set_flags, br_initbits, zrq, zr_gist.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits
       s_hdr s_win s_cur s_tab s_bld s_hold s_bits
       h_mode h_last h_wrap h_havedict h_flags h_dmax h_check h_total h_head].
  f_equal; first [reflexivity | lia | f_equal; first [reflexivity | lia]].
Qed.

Lemma zr_gz_os_arm : forall z rest obuf put cap,
  inf_OS (zrq (zr_gist M_OS 0 8 zr_gz_ck2 0) z
              (zr_gzip_header 9 ++ rest) 8 obuf put cap)
  = inf_EXLEN (zrq (zr_gist M_EXLEN 0 8 zr_gz_ck2 0) z
                   (zr_gzip_header 9 ++ rest) 10 obuf put cap).
Proof.
  intros z rest obuf put cap.
  assert (Hr : 0 <= zlen rest) by (unfold zlen; lia).
  assert (Hlen : zlen (zr_gzip_header 9 ++ rest) = 10 + zlen rest)
    by (rewrite zlen_app, zr_gz_hdr_len; reflexivity).
  unfold inf_OS.
  unfold zrq at 1. cbn [q_st q_br].
  rewrite inf_nb_pull2 by lia.
  cbn [s_hdr h_flags zr_gist].
  replace (Z.land 8 512) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  cbn [negb andb].
  f_equal.
  unfold qmode, qset_br, qset_st, set_mode, set_flags, br_initbits, zrq, zr_gist.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits
       s_hdr s_win s_cur s_tab s_bld s_hold s_bits
       h_mode h_last h_wrap h_havedict h_flags h_dmax h_check h_total h_head].
  f_equal; first [reflexivity | lia | f_equal; first [reflexivity | lia]].
Qed.

(** ---- step 2 composed: one [inf_step] from M_FLAGS to M_TYPE. ---- *)
Lemma zr_gz_step_flags : forall z rest obuf put cap, exists z',
  inf_step zr_ic (zrq (zr_gist M_FLAGS 0 (-1) zr_gz_ck2 0) z
                      (zr_gzip_header 9 ++ rest) 2 obuf put cap)
  = InfCont (zrq (zr_gist M_TYPE 0 8 (crc32_z 0 true 0 []) 0) z'
                 (zr_gzip_header 9 ++ rest) 10 obuf put cap).
Proof.
  intros z rest obuf put cap.
  eexists.
  unfold inf_step.
  replace (q_mode (zrq (zr_gist M_FLAGS 0 (-1) zr_gz_ck2 0) z
                       (zr_gzip_header 9 ++ rest) 2 obuf put cap))
    with M_FLAGS by reflexivity.
  cbv iota.
  rewrite zr_gz_flags_arm, zr_gz_time_arm, zr_gz_os_arm.
  rewrite zr_gz_exlen_skip, zr_gz_extra_skip, zr_gz_name_skip,
          zr_gz_comment_skip, zr_gz_hcrc_skip.
  reflexivity.
Qed.

(** ---- THE entry: init at 31, two steps, ten bytes, M_TYPE. ---- *)
Lemma zr_gz_entry : forall z rest obuf put cap, exists z2,
  inf_iter 2 zr_ic (zrq (zr_gist M_HEAD 0 (-1) 0 0) z
                        (zr_gzip_header 9 ++ rest) 0 obuf put cap)
  = Some (zrq (zr_gist M_TYPE 0 8 (crc32_z 0 true 0 []) 0) z2
              (zr_gzip_header 9 ++ rest) 10 obuf put cap).
Proof.
  intros z rest obuf put cap.
  destruct (zr_gz_step_head z rest obuf put cap) as [z1 S1].
  destruct (zr_gz_step_flags z1 rest obuf put cap) as [z2 S2].
  exists z2.
  cbn [inf_iter]. rewrite S1. cbv iota. rewrite S2. cbv iota. reflexivity.
Qed.

Print Assumptions zr_gz_entry.
