(** * ZReproL0C — config (0, 15): the one-shot inflate walk over the
    stored-block stream, i.e. the read half of the (0,15) round trip:

      zr_inflate Z_FINISH 15 cap (zr_l0_stream x) = Some (map u8 x)

    The mode-machine path is HEAD -> TYPE -> (TYPEDO STORED COPY_ COPY+)*
    -> CHECK -> LENGTH -> DONE, with the input read one-shot (every COPY
    consumes its whole block: avail_in covers the stream and avail_out
    covers the payload), so the window is never consulted and the walk is
    an induction over blocks with hold/bits empty at every block
    boundary. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk ZBitsIn ZBitsOut InflateFast Inflate Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  GtAdlerChunk GtAdlerLoop ZRepro ZReproL0 ZReproL0B.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The context of the [zr_inflate] call. *)
Definition zr_ic : InfCtx :=
  {| n_flush := Z_FINISH; n_walloc := true; n_wfresh := zzero |}.

(** The walk's [InfSt] shape: input array fixed to the whole stream,
    reader at [nxt] with an empty accumulator, output at [put]. *)
Definition zrq (st : IState) (z : Strm) (stream : list Z)
               (nxt : Z) (obuf : zarr) (put cap : Z) : InfSt :=
  {| q_st := st; q_z := z;
     q_br := {| br_in := zlist stream; br_have := zlen stream - nxt;
                br_next := nxt; br_hold := 0; br_bits := 0 |};
     q_ob := {| o_buf := obuf; o_put := put; o_left := cap - put |};
     q_in := zlen stream; q_out := cap; q_ret := Z_OK |}.

(** The post-init inflate state at windowBits 15 — closed. *)
Definition zr_ist0 : IState :=
  match inflateInit2 z_fresh state_fresh 15 with
  | Some (_, s) => s
  | None => state_fresh
  end.

Definition zr_z0 : Strm :=
  match inflateInit2 z_fresh state_fresh 15 with
  | Some (z, _) => z
  | None => z_fresh
  end.

Lemma zr_init_15 :
  inflateInit2 z_fresh state_fresh 15 = Some (zr_z0, zr_ist0).
Proof. vm_compute. reflexivity. Qed.

(** The walk's [IState]: everything closed except the mode, BFINAL flag,
    the stored-copy length counter, the running total and the check.
    Extracted from a [vm_compute] of the post-init and post-HEAD states. *)
Definition zr_ist (m : Mode) (last len total check : Z) : IState :=
  {| s_hdr := {| h_mode := m; h_last := last; h_wrap := 5; h_havedict := 0;
                 h_flags := 0; h_dmax := 32768; h_check := check;
                 h_total := total; h_head := 0 |};
     s_win := {| w_wbits := 15; w_wsize := 0; w_whave := 0; w_wnext := 0;
                 w_alloc := false; w_win := zzero |};
     s_cur := {| u_length := len; u_offset := 0; u_extra := 0; u_back := -1;
                 u_was := 0 |};
     s_tab := {| t_lencode := TRcodes 0; t_distcode := TRcodes 0;
                 t_lenbits := 0; t_distbits := 0; t_next := 0;
                 t_codes := tnone; t_sane := 1 |};
     s_bld := {| b_ncode := 0; b_nlen := 0; b_ndist := 0; b_have := 0;
                 b_lens := zzero; b_work := zzero |};
     s_hold := 0; s_bits := 0 |}.

Lemma zlen_cons : forall (a : Z) l, zlen (a :: l) = 1 + zlen l.
Proof. intros a l. unfold zlen. cbn [length]. lia. Qed.

Lemma zlen_app : forall (l1 l2 : list Z), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros l1 l2. unfold zlen. rewrite length_app. lia. Qed.

(** [inf_nb] on an empty accumulator: the pull loop, once per byte.
    Generic in the array, position and remaining count, so every arm's
    NEEDBITS is one rewrite. *)
Lemma inf_nb_pull1 : forall (n : Z) (arr : zarr) have nxt,
  0 < n <= 8 -> 1 <= have ->
  inf_nb n {| br_in := arr; br_have := have; br_next := nxt;
              br_hold := 0; br_bits := 0 |}
  = NBOk {| br_in := arr; br_have := have - 1; br_next := nxt + 1;
            br_hold := Z.shiftl (arr nxt) 0 + 0; br_bits := 8 |}.
Proof.
  intros n arr have nxt Hn Hh.
  unfold inf_nb.
  destruct (Z.to_nat n) as [|f] eqn:Ef; [exfalso; lia|].
  cbn [inf_nb_go].
  cbn [br_bits].
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold br_pullbyte. cbn [br_have br_in br_next br_hold br_bits].
  replace (have =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct f as [|f]; cbn [inf_nb_go br_bits];
    replace (0 + 8 <? n) with false by (symmetry; apply Z.ltb_ge; lia);
    (f_equal; f_equal; first [reflexivity | lia]).
Qed.

Lemma inf_nb_pull2 : forall (n : Z) (arr : zarr) have nxt,
  8 < n <= 16 -> 2 <= have ->
  inf_nb n {| br_in := arr; br_have := have; br_next := nxt;
              br_hold := 0; br_bits := 0 |}
  = NBOk {| br_in := arr; br_have := have - 2; br_next := nxt + 2;
            br_hold := Z.shiftl (arr nxt) 0 + Z.shiftl (arr (nxt + 1)) 8;
            br_bits := 16 |}.
Proof.
  intros n arr have nxt Hn Hh.
  unfold inf_nb.
  destruct (Z.to_nat n) as [|f] eqn:Ef; [exfalso; lia|].
  cbn [inf_nb_go br_bits].
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold br_pullbyte. cbn [br_have br_in br_next br_hold br_bits].
  replace (have =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct f as [|f]; [exfalso; lia|].
  cbn [inf_nb_go br_bits].
  replace (0 + 8 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold br_pullbyte. cbn [br_have br_in br_next br_hold br_bits].
  replace (have - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct f as [|f]; cbn [inf_nb_go br_bits];
    replace (0 + 8 + 8 <? n) with false by (symmetry; apply Z.ltb_ge; lia);
    replace (0 + 8) with 8 by reflexivity;
    (f_equal; f_equal; first [reflexivity | lia]).
Qed.

Lemma inf_nb_pull4 : forall (n : Z) (arr : zarr) have nxt,
  24 < n <= 32 -> 4 <= have ->
  inf_nb n {| br_in := arr; br_have := have; br_next := nxt;
              br_hold := 0; br_bits := 0 |}
  = NBOk {| br_in := arr; br_have := have - 4; br_next := nxt + 4;
            br_hold := Z.shiftl (arr nxt) 0 + Z.shiftl (arr (nxt + 1)) 8
                       + Z.shiftl (arr (nxt + 2)) 16
                       + Z.shiftl (arr (nxt + 3)) 24;
            br_bits := 32 |}.
Proof.
  intros n arr have nxt Hn Hh.
  unfold inf_nb.
  destruct (Z.to_nat n) as [|f] eqn:Ef; [exfalso; lia|].
  cbn [inf_nb_go br_bits].
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold br_pullbyte. cbn [br_have br_in br_next br_hold br_bits].
  replace (have =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct f as [|f]; [exfalso; lia|].
  cbn [inf_nb_go br_bits].
  replace (0 + 8 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold br_pullbyte. cbn [br_have br_in br_next br_hold br_bits].
  replace (have - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct f as [|f]; [exfalso; lia|].
  cbn [inf_nb_go br_bits].
  replace (0 + 8 + 8 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold br_pullbyte. cbn [br_have br_in br_next br_hold br_bits].
  replace (have - 1 - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct f as [|f]; [exfalso; lia|].
  cbn [inf_nb_go br_bits].
  replace (0 + 8 + 8 + 8 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold br_pullbyte. cbn [br_have br_in br_next br_hold br_bits].
  replace (have - 1 - 1 - 1 =? 0) with false
    by (symmetry; apply Z.eqb_neq; lia).
  destruct f as [|f]; cbn [inf_nb_go br_bits];
    replace (0 + 8 + 8 + 8 + 8 <? n) with false
      by (symmetry; apply Z.ltb_ge; lia);
    replace (0 + 8 + 8 + 8) with 24 by reflexivity;
    replace (0 + 8 + 8) with 16 by reflexivity;
    replace (0 + 8) with 8 by reflexivity;
    replace (nxt + 1 + 1 + 1) with (nxt + 3) by lia;
    replace (nxt + 1 + 1) with (nxt + 2) by lia;
    (f_equal; f_equal; first [reflexivity | lia]).
Qed.

(** The HEAD step on the [120; 1] header: both bytes in, all checks pass,
    check seeds to adler(0,NULL) = 1, mode TYPE, reader at byte 2.  The
    [Strm] mirror field evolves too but nothing in the walk branches on
    it, so it is existential. *)
Lemma zr_step_head : forall z rest obuf cap, exists z',
  inf_step zr_ic (zrq zr_ist0 z (120 :: 1 :: rest) 0 obuf 0 cap)
  = InfCont (zrq (zr_ist M_TYPE 0 0 0 1) z' (120 :: 1 :: rest) 2 obuf 0 cap).
Proof.
  intros z rest obuf cap.
  pose proof (zlen_nonneg rest) as Hr.
  eexists.
  unfold inf_step.
  replace (q_mode (zrq zr_ist0 z (120 :: 1 :: rest) 0 obuf 0 cap))
    with M_HEAD by reflexivity.
  unfold inf_HEAD. cbv zeta.
  unfold zrq. cbn [q_st q_br].
  replace (h_wrap (s_hdr zr_ist0)) with 5 by reflexivity.
  replace (5 =? 0) with false by reflexivity.
  rewrite !zlen_cons.
  rewrite inf_nb_pull2 by lia.
  replace (zlist (120 :: 1 :: rest) 0) with 120 by reflexivity.
  replace (zlist (120 :: 1 :: rest) (0 + 1)) with 1 by reflexivity.
  cbn [br_hold br_bits br_in br_next br_have].
  replace (Z.shiftl 120 0 + Z.shiftl 1 8) with 376 by reflexivity.
  replace (Z.land 5 2) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  replace (376 =? 35615) with false by reflexivity.
  cbn [negb andb].
  replace (Z.land 5 1) with 1 by reflexivity.
  replace (1 =? 0) with false by reflexivity.
  unfold br_bits_of.
  cbn [br_hold].
  replace (Z.land 376 (Z.shiftl 1 8 - 1)) with 120 by reflexivity.
  replace (Z.shiftl 120 8) with 30720 by reflexivity.
  replace (Z.shiftr 376 8) with 1 by reflexivity.
  replace (30720 + 1) with 30721 by reflexivity.
  replace (30721 mod 31) with 0 by reflexivity.
  cbn [negb orb].
  replace (Z.land 376 (Z.shiftl 1 4 - 1)) with 8 by reflexivity.
  replace (8 =? Z_DEFLATED) with true by reflexivity.
  cbn [negb].
  unfold br_dropbits. cbn [br_hold br_bits br_in br_next br_have].
  replace (Z.shiftr 376 4) with 23 by reflexivity.
  replace (Z.land 23 (Z.shiftl 1 4 - 1)) with 7 by reflexivity.
  replace (7 + 8) with 15 by reflexivity.
  replace (w_wbits (s_win zr_ist0)) with 15 by reflexivity.
  replace (15 =? 0) with false by reflexivity.
  replace (15 <? 15) with false by reflexivity.
  cbn [negb orb].
  replace (0 =? 0) with true by reflexivity.
  cbn [negb].
  replace (w_wbits (s_win zr_ist0)) with 15 by reflexivity.
  replace (15 <? 15) with false by reflexivity.
  cbn [negb orb].
  replace (Z.land 23 512) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  unfold qcheck, qmode, qset_br, qset_st, qset_z, br_initbits.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits].
  f_equal.
  unfold zrq, zr_ist.
  f_equal; first [reflexivity | lia | f_equal; first [reflexivity | lia]].
Qed.

(** Mid-block reader states carry pending bits, so the walk's general
    state adds the accumulator. *)
Definition zrqb (st : IState) (z : Strm) (stream : list Z)
                (nxt hold bits : Z) (obuf : zarr) (put cap : Z) : InfSt :=
  {| q_st := st; q_z := z;
     q_br := {| br_in := zlist stream; br_have := zlen stream - nxt;
                br_next := nxt; br_hold := hold; br_bits := bits |};
     q_ob := {| o_buf := obuf; o_put := put; o_left := cap - put |};
     q_in := zlen stream; q_out := cap; q_ret := Z_OK |}.

Lemma zrq_b : forall st z stream nxt obuf put cap,
  zrq st z stream nxt obuf put cap = zrqb st z stream nxt 0 0 obuf put cap.
Proof. reflexivity. Qed.

(** TYPE falls through to TYPEDO at Z_FINISH; on a stored block the three
    type bits come from one pulled byte [lastb] (0 or 1: BTYPE = 00), and
    the arm leaves [lastb >> 3 = 0] in a five-bit accumulator. *)
Lemma zr_step_type : forall lastb len tot chk z stream nxt obuf put cap,
  0 <= lastb <= 1 ->
  zlist stream nxt = lastb ->
  1 <= zlen stream - nxt ->
  inf_step zr_ic (zrq (zr_ist M_TYPE 0 len tot chk) z stream nxt obuf put cap)
  = InfCont (zrqb (zr_ist M_STORED lastb len tot chk) z stream (nxt + 1)
                  0 5 obuf put cap).
Proof.
  intros lastb len tot chk z stream nxt obuf put cap Hl Hb Hh.
  unfold inf_step.
  replace (q_mode (zrq (zr_ist M_TYPE 0 len tot chk) z stream nxt obuf put cap))
    with M_TYPE by reflexivity.
  unfold inf_TYPE.
  replace (n_flush zr_ic =? Z_BLOCK) with false by reflexivity.
  replace (n_flush zr_ic =? Z_TREES) with false by reflexivity.
  cbn [orb].
  unfold inf_TYPEDO. cbv zeta.
  unfold zrq. cbn [q_st q_br].
  replace (h_last (s_hdr (zr_ist M_TYPE 0 len tot chk))) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  cbn [negb].
  rewrite inf_nb_pull1 by lia.
  rewrite Hb.
  unfold br_bits_of, br_dropbits.
  cbn [br_hold br_bits br_in br_next br_have].
  assert (HL : lastb = 0 \/ lastb = 1) by lia.
  destruct HL as [-> | ->];
  [ replace (Z.shiftl 0 0 + 0) with 0 by reflexivity;
    replace (Z.shiftr 0 1) with 0 by reflexivity;
    replace (Z.land 0 (Z.shiftl 1 2 - 1)) with 0 by reflexivity;
    replace (Z.land 0 (Z.shiftl 1 1 - 1)) with 0 by reflexivity
  | replace (Z.shiftl 1 0 + 0) with 1 by reflexivity;
    replace (Z.shiftr 1 1) with 0 by reflexivity;
    replace (Z.land 0 (Z.shiftl 1 2 - 1)) with 0 by reflexivity;
    replace (Z.land 1 (Z.shiftl 1 1 - 1)) with 1 by reflexivity ];
  replace (0 =? 0) with true by reflexivity;
  replace (n_flush zr_ic =? Z_TREES) with false by reflexivity;
  unfold qmode, qset_br, qset_st;
  cbn [q_st q_z q_br q_ob q_in q_out q_ret];
  f_equal;
  unfold zrqb, zr_ist;
  (f_equal; first [reflexivity | lia
                  | f_equal; first [reflexivity | lia]]).
Qed.

(** The LEN/NLEN arithmetic: the four little-endian header bytes
    reassemble to [len] and its ones-complement, and the arm's check and
    extraction both come out exact. *)
Lemma zr_hold4 : forall b0 b1 b2 b3,
  Z.shiftl b0 0 + Z.shiftl b1 8 + Z.shiftl b2 16 + Z.shiftl b3 24
  = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof.
  intros b0 b1 b2 b3.
  rewrite !Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 0) with 1 by reflexivity.
  replace (2 ^ 8) with 256 by reflexivity.
  replace (2 ^ 16) with 65536 by reflexivity.
  replace (2 ^ 24) with 16777216 by reflexivity.
  lia.
Qed.

Lemma zr_neg_mod : forall len m,
  0 <= len -> 0 < m -> len < m ->
  (- len - 1) mod m = m - 1 - len.
Proof.
  intros len m Hl Hm Hlm.
  replace (- len - 1) with ((m - 1 - len) + (-1) * m) by lia.
  rewrite Z_mod_plus_full.
  apply Z.mod_small. lia.
Qed.

Lemma zr_len_bytes : forall len,
  0 <= len <= 65535 ->
  u8 len + 256 * u8 (Z.shiftr len 8) = len.
Proof.
  intros len Hl. unfold u8.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 8) with 256 by reflexivity.
  rewrite (Z.mod_small (len / 256) 256)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.div_mod len 256) at 3 by lia. lia.
Qed.

Lemma zr_nlen_bytes : forall len,
  0 <= len <= 65535 ->
  u8 (Z.lnot len) + 256 * u8 (Z.shiftr (u32 (Z.lnot len)) 8) = 65535 - len.
Proof.
  intros len Hl.
  unfold u8, u32.
  replace (Z.lnot len) with (- len - 1) by (unfold Z.lnot; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 8) with 256 by reflexivity.
  set (q := len / 256). set (r := len mod 256).
  assert (Hqr : len = 256 * q + r) by (apply Z.div_mod; lia).
  assert (Hr : 0 <= r < 256) by (apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= q <= 255)
    by (split; [apply Z.div_pos; lia | ];
        assert (len / 256 <= 65535 / 256) by (apply Z.div_le_mono; lia);
        subst q; vm_compute (65535 / 256) in *; lia).
  replace ((- len - 1) mod 256) with (255 - r).
  2:{ replace (- len - 1) with ((255 - r) + (- q - 1) * 256) by lia.
      rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
  rewrite (zr_neg_mod len 4294967296) by lia.
  replace (4294967296 - 1 - len) with ((255 - r) + (16777216 - q - 1) * 256)
    by lia.
  rewrite Z.div_add by lia.
  rewrite (Z.div_small (255 - r) 256) by lia.
  replace (0 + (16777216 - q - 1)) with ((255 - q) + 65535 * 256) by lia.
  rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (255 - q) 256) by lia.
  lia.
Qed.

(** [x XOR 0xffff] on the complement gives the length back. *)
Lemma zr_lxor_comp : forall len,
  0 <= len <= 65535 ->
  Z.lxor (65535 - len) 65535 = len.
Proof.
  intros len Hl.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec.
  destruct (Z.ltb i 16) eqn:Ei.
  - apply Z.ltb_lt in Ei.
    replace 65535 with (Z.ones 16) by reflexivity.
    rewrite (Z.ones_spec_low 16 i) by lia.
    replace (Z.ones 16 - len) with (Z.land (Z.lnot len) (Z.ones 16)).
    2:{ rewrite Z.land_ones by lia.
        replace (Z.lnot len) with (- len - 1) by (unfold Z.lnot; lia).
        replace (2 ^ 16) with 65536 by reflexivity.
        rewrite (zr_neg_mod len 65536) by lia.
        replace (Z.ones 16) with 65535 by reflexivity. lia. }
    rewrite Z.land_spec, Z.lnot_spec by lia.
    rewrite (Z.ones_spec_low 16 i) by lia.
    rewrite andb_true_r.
    now destruct (Z.testbit len i).
  - apply Z.ltb_ge in Ei.
    replace 65535 with (Z.ones 16) by reflexivity.
    rewrite (Z.ones_spec_high 16 i) by lia.
    rewrite xorb_false_r.
    rewrite (Z.bits_above_log2 (Z.ones 16 - len) i); cycle 1.
    { replace (Z.ones 16) with 65535 by reflexivity. lia. }
    { assert (Z.ones 16 - len <= 65535)
        by (replace (Z.ones 16) with 65535 by reflexivity; lia).
      assert (Z.log2 (Z.ones 16 - len) < 16); [|lia].
      destruct (Z.eqb (Z.ones 16 - len) 0) eqn:E0.
      - apply Z.eqb_eq in E0. rewrite E0. vm_compute (Z.log2 0). lia.
      - apply Z.eqb_neq in E0.
        assert (Z.log2 (Z.ones 16 - len) <= Z.log2 65535)
          by (apply Z.log2_le_mono; lia).
        vm_compute (Z.log2 65535) in *. lia. }
    symmetry.
    apply (Z.bits_above_log2 len i); [lia|].
    destruct (Z.eqb len 0) eqn:E0.
    + apply Z.eqb_eq in E0. rewrite E0. vm_compute (Z.log2 0). lia.
    + apply Z.eqb_neq in E0.
      assert (Z.log2 len <= Z.log2 65535) by (apply Z.log2_le_mono; lia).
      vm_compute (Z.log2 65535) in *. lia.
Qed.

Lemma zr_land16 : forall lo hi, 0 <= lo < 65536 -> 0 <= hi ->
  Z.land (lo + 65536 * hi) 65535 = lo.
Proof.
  intros lo hi Hlo Hhi.
  replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia.
  replace (2 ^ 16) with 65536 by reflexivity.
  replace (lo + 65536 * hi) with (lo + hi * 65536) by lia.
  rewrite Z_mod_plus_full.
  apply Z.mod_small. lia.
Qed.

Lemma zr_shiftr16 : forall lo hi, 0 <= lo < 65536 -> 0 <= hi ->
  Z.shiftr (lo + 65536 * hi) 16 = hi.
Proof.
  intros lo hi Hlo Hhi.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 16) with 65536 by reflexivity.
  replace (lo + 65536 * hi) with (lo + hi * 65536) by lia.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

(** The STORED arm on a positive-length block: bytebits, four header
    bytes, LEN/NLEN check, and the WHOLE payload copy (the arm falls
    through COPY_ into COPY inline, and one-shot input/output cover the
    block). *)
Lemma zr_step_stored : forall lastb len tot chk z stream nxt obuf put cap,
  0 < len <= 65535 ->
  0 <= nxt -> 0 <= put ->
  zlist stream nxt = u8 len ->
  zlist stream (nxt + 1) = u8 (Z.shiftr len 8) ->
  zlist stream (nxt + 2) = u8 (Z.lnot len) ->
  zlist stream (nxt + 3) = u8 (Z.shiftr (u32 (Z.lnot len)) 8) ->
  4 + len <= zlen stream - nxt ->
  len <= cap - put ->
  inf_step zr_ic
    (zrqb (zr_ist M_STORED lastb 0 tot chk) z stream nxt 0 5 obuf put cap)
  = InfCont (zrq (zr_ist M_COPY lastb 0 tot chk) z stream (nxt + 4 + len)
                 (zcopy (Z.to_nat len) obuf put (zlist stream) (nxt + 4))
                 (put + len) cap).
Proof.
  intros lastb len tot chk z stream nxt obuf put cap
         Hlen Hnxt Hput Hb0 Hb1 Hb2 Hb3 Hin Hout.
  assert (Hu8len : 0 <= u8 len < 256) by (unfold u8; apply Z.mod_pos_bound; lia).
  assert (Hu8l1 : 0 <= u8 (Z.shiftr len 8) < 256)
    by (unfold u8; apply Z.mod_pos_bound; lia).
  assert (Hu8l2 : 0 <= u8 (Z.lnot len) < 256)
    by (unfold u8; apply Z.mod_pos_bound; lia).
  assert (Hu8l3 : 0 <= u8 (Z.shiftr (u32 (Z.lnot len)) 8) < 256)
    by (unfold u8; apply Z.mod_pos_bound; lia).
  pose proof (zr_len_bytes len ltac:(lia)) as Elo.
  pose proof (zr_nlen_bytes len ltac:(lia)) as Ehi.
  unfold inf_step.
  replace (q_mode (zrqb (zr_ist M_STORED lastb 0 tot chk) z stream nxt 0 5
                        obuf put cap))
    with M_STORED by reflexivity.
  unfold inf_STORED. cbv zeta.
  unfold zrqb. cbn [q_st q_br].
  unfold br_bytebits, br_dropbits.
  cbn [br_bits br_hold br_in br_next br_have].
  replace (Z.land 5 7) with 5 by reflexivity.
  replace (Z.shiftr 0 5) with 0 by reflexivity.
  replace (5 - 5) with 0 by reflexivity.
  rewrite inf_nb_pull4 by lia.
  rewrite Hb0, Hb1, Hb2, Hb3.
  cbn [br_hold br_bits br_in br_next br_have].
  rewrite zr_hold4.
  replace (u8 len + 256 * u8 (Z.shiftr len 8) + 65536 * u8 (Z.lnot len)
           + 16777216 * u8 (Z.shiftr (u32 (Z.lnot len)) 8))
    with ((u8 len + 256 * u8 (Z.shiftr len 8))
          + 65536 * (u8 (Z.lnot len)
                     + 256 * u8 (Z.shiftr (u32 (Z.lnot len)) 8))) by lia.
  rewrite zr_land16 by lia.
  rewrite zr_shiftr16 by lia.
  rewrite Elo, Ehi.
  rewrite zr_lxor_comp by lia.
  replace (len =? len) with true by (symmetry; apply Z.eqb_refl).
  cbn [negb].
  replace (n_flush zr_ic =? Z_TREES) with false by reflexivity.
  replace (u32 (len + 65536 * (65535 - len)))
    with (len + 65536 * (65535 - len))
    by (unfold u32; symmetry; apply Z.mod_small; lia).
  rewrite zr_land16 by lia.
  unfold inf_COPY_, inf_COPY. cbv zeta.
  unfold qmode, qset_st, qset_br, br_initbits.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits
       o_buf o_put o_left s_hdr s_cur].
  replace (u_length (s_cur (set_mode (set_mode
             (set_length (zr_ist M_STORED lastb 0 tot chk) len)
             M_COPY_) M_COPY)))
    with len by reflexivity.
  replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (zlen stream - nxt - 4 <? len) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (cap - put <? len) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (len - len) with 0 by lia.
  replace (u32 0) with 0 by reflexivity.
  replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold qset_ob, qset_br, qset_st.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret o_buf o_put o_left].
  f_equal.
  unfold zrq, zr_ist.
  (f_equal; first [reflexivity | lia
                  | f_equal; first [reflexivity | lia]]).
Qed.

(** COPY with an exhausted counter hands control back to TYPE. *)
Lemma zr_step_copy0 : forall lastb tot chk z stream nxt obuf put cap,
  inf_step zr_ic (zrq (zr_ist M_COPY lastb 0 tot chk) z stream nxt obuf put cap)
  = InfCont (zrq (zr_ist M_TYPE lastb 0 tot chk) z stream nxt obuf put cap).
Proof.
  intros lastb tot chk z stream nxt obuf put cap.
  unfold inf_step.
  replace (q_mode (zrq (zr_ist M_COPY lastb 0 tot chk) z stream nxt obuf put cap))
    with M_COPY by reflexivity.
  unfold inf_COPY. cbv zeta.
  unfold zrq. cbn [q_st q_br s_cur].
  replace (u_length (s_cur (zr_ist M_COPY lastb 0 tot chk))) with 0
    by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  unfold qmode, qset_st.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret].
  f_equal.
Qed.

(** The STORED arm on the empty final block ([len = 0]; the inline COPY
    sees an exhausted counter and hands straight back to TYPE). *)
Lemma zr_step_stored0 : forall lastb tot chk z stream nxt obuf put cap,
  0 <= nxt ->
  zlist stream nxt = 0 ->
  zlist stream (nxt + 1) = 0 ->
  zlist stream (nxt + 2) = 255 ->
  zlist stream (nxt + 3) = 255 ->
  4 <= zlen stream - nxt ->
  inf_step zr_ic
    (zrqb (zr_ist M_STORED lastb 0 tot chk) z stream nxt 0 5 obuf put cap)
  = InfCont (zrq (zr_ist M_TYPE lastb 0 tot chk) z stream (nxt + 4)
                 obuf put cap).
Proof.
  intros lastb tot chk z stream nxt obuf put cap Hnxt Hb0 Hb1 Hb2 Hb3 Hin.
  unfold inf_step.
  replace (q_mode (zrqb (zr_ist M_STORED lastb 0 tot chk) z stream nxt 0 5
                        obuf put cap))
    with M_STORED by reflexivity.
  unfold inf_STORED. cbv zeta.
  unfold zrqb. cbn [q_st q_br].
  unfold br_bytebits, br_dropbits.
  cbn [br_bits br_hold br_in br_next br_have].
  replace (Z.land 5 7) with 5 by reflexivity.
  replace (Z.shiftr 0 5) with 0 by reflexivity.
  replace (5 - 5) with 0 by reflexivity.
  rewrite inf_nb_pull4 by lia.
  rewrite Hb0, Hb1, Hb2, Hb3.
  cbn [br_hold br_bits br_in br_next br_have].
  replace (Z.shiftl 0 0 + Z.shiftl 0 8 + Z.shiftl 255 16 + Z.shiftl 255 24)
    with 4294901760 by reflexivity.
  replace (Z.land 4294901760 65535) with 0 by reflexivity.
  replace (Z.lxor (Z.shiftr 4294901760 16) 65535) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  cbn [negb].
  replace (n_flush zr_ic =? Z_TREES) with false by reflexivity.
  replace (u32 4294901760) with 4294901760 by reflexivity.
  replace (Z.land 4294901760 65535) with 0 by reflexivity.
  unfold inf_COPY_, inf_COPY. cbv zeta.
  unfold qmode, qset_st, qset_br, br_initbits.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits s_cur].
  replace (u_length (s_cur (set_mode (set_mode
             (set_length (zr_ist M_STORED lastb 0 tot chk) 0)
             M_COPY_) M_COPY)))
    with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  f_equal.
  unfold zrq, zr_ist.
  (f_equal; first [reflexivity | lia
                  | f_equal; first [reflexivity | lia]]).
Qed.

(** TYPE at the end of the last block: BFINAL is set, so TYPEDO goes to
    CHECK (bits already byte-aligned at a block boundary). *)
Lemma zr_step_type_final : forall len tot chk z stream nxt obuf put cap,
  inf_step zr_ic (zrq (zr_ist M_TYPE 1 len tot chk) z stream nxt obuf put cap)
  = InfCont (zrq (zr_ist M_CHECK 1 len tot chk) z stream nxt obuf put cap).
Proof.
  intros len tot chk z stream nxt obuf put cap.
  unfold inf_step.
  replace (q_mode (zrq (zr_ist M_TYPE 1 len tot chk) z stream nxt obuf put cap))
    with M_TYPE by reflexivity.
  unfold inf_TYPE.
  replace (n_flush zr_ic =? Z_BLOCK) with false by reflexivity.
  replace (n_flush zr_ic =? Z_TREES) with false by reflexivity.
  cbn [orb].
  unfold inf_TYPEDO.
  replace (h_last (s_hdr (q_st (zrq (zr_ist M_TYPE 1 len tot chk) z stream nxt
                                    obuf put cap))))
    with 1 by reflexivity.
  replace (1 =? 0) with false by reflexivity.
  cbn [negb].
  unfold zrq, br_bytebits, br_dropbits, qmode, qset_br, qset_st.
  cbn [q_st q_z q_br q_ob q_in q_out q_ret
       br_in br_have br_next br_hold br_bits].
  replace (Z.land 0 7) with 0 by reflexivity.
  replace (Z.shiftr 0 0) with 0 by reflexivity.
  replace (0 - 0) with 0 by reflexivity.
  f_equal.
Qed.

(** Mask-shift identity for the middle byte of [zswap32]. *)
Lemma zr_land_ff00 : forall X,
  Z.land X 65280 = Z.shiftl (Z.land (Z.shiftr X 8) 255) 8.
Proof.
  intro X. apply Z.bits_inj'. intros i Hi.
  replace 65280 with (Z.shiftl 255 8) by reflexivity.
  rewrite Z.land_spec.
  destruct (Z.leb 8 i) eqn:E8.
  - apply Z.leb_le in E8.
    rewrite (Z.shiftl_spec 255 8 i) by lia.
    rewrite (Z.shiftl_spec _ 8 i) by lia.
    rewrite Z.land_spec.
    rewrite Z.shiftr_spec by lia.
    replace (i - 8 + 8) with i by lia.
    reflexivity.
  - apply Z.leb_gt in E8.
    rewrite (Z.shiftl_spec 255 8 i) by lia.
    rewrite (Z.shiftl_spec _ 8 i) by lia.
    rewrite (Z.testbit_neg_r 255 (i - 8)) by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
    now rewrite andb_false_r.
Qed.

(** [zswap32] undoes the little-endian read of a big-endian word. *)
Lemma zr_zswap32_be : forall AD, 0 <= AD < 4294967296 ->
  zswap32 (Z.shiftl (u8 (AD / 16777216)) 0 + Z.shiftl (u8 (AD / 65536)) 8
           + Z.shiftl (u8 (AD / 256)) 16 + Z.shiftl (u8 AD) 24) = AD.
Proof.
  intros AD HAD.
  rewrite zr_hold4.
  unfold u8.
  set (a0 := AD mod 256).
  set (a1 := (AD / 256) mod 256).
  set (a2 := (AD / 65536) mod 256).
  set (a3 := AD / 16777216).
  assert (Ha0 : 0 <= a0 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Ha1 : 0 <= a1 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Ha2 : 0 <= a2 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Ha3 : 0 <= a3 < 256)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hd1 : AD = 256 * (AD / 256) + a0) by (apply Z.div_mod; lia).
  assert (Hd2 : AD / 256 = 256 * (AD / 65536) + a1).
  { replace (AD / 65536) with (AD / 256 / 256)
      by (rewrite Z.div_div by lia; f_equal).
    apply Z.div_mod; lia. }
  assert (Hd3 : AD / 65536 = 256 * a3 + a2).
  { replace a3 with (AD / 65536 / 256)
      by (subst a3; rewrite Z.div_div by lia; f_equal).
    apply Z.div_mod; lia. }
  replace (a3 mod 256) with a3 by (symmetry; apply Z.mod_small; lia).
  set (HOLD := a3 + 256 * a2 + 65536 * a1 + 16777216 * a0).
  assert (HH : 0 <= HOLD < 4294967296) by (subst HOLD; lia).
  unfold zswap32.
  assert (E24 : Z.shiftr HOLD 24 = a0).
  { rewrite Z.shiftr_div_pow2 by lia.
    replace (2 ^ 24) with 16777216 by reflexivity.
    replace HOLD with ((a3 + 256 * a2 + 65536 * a1) + a0 * 16777216)
      by (subst HOLD; lia).
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia. }
  assert (E8 : Z.shiftr HOLD 8 = a2 + 256 * a1 + 65536 * a0).
  { rewrite Z.shiftr_div_pow2 by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    replace HOLD with (a3 + (a2 + 256 * a1 + 65536 * a0) * 256)
      by (subst HOLD; lia).
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia. }
  rewrite E24, E8.
  replace (Z.land a0 255) with a0.
  2:{ replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
  rewrite zr_land_ff00.
  replace (Z.shiftr (a2 + 256 * a1 + 65536 * a0) 8) with (a1 + 256 * a0).
  2:{ rewrite Z.shiftr_div_pow2 by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      replace (a2 + 256 * a1 + 65536 * a0)
        with (a2 + (a1 + 256 * a0) * 256) by lia.
      rewrite Z.div_add by lia.
      rewrite Z.div_small by lia. lia. }
  replace (Z.land (a1 + 256 * a0) 255) with a1.
  2:{ replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      replace (a1 + 256 * a0) with (a1 + a0 * 256) by lia.
      rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
  rewrite zr_land_ff00.
  replace (Z.shiftr HOLD 8) with (a2 + 256 * a1 + 65536 * a0) by (symmetry; exact E8).
  replace (Z.land (a2 + 256 * a1 + 65536 * a0) 255) with a2.
  2:{ replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      replace (a2 + 256 * a1 + 65536 * a0)
        with (a2 + (a1 + 256 * a0) * 256) by lia.
      rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
  replace (Z.land HOLD 255) with a3.
  2:{ replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      replace HOLD with (a3 + (a2 + 256 * a1 + 65536 * a0) * 256)
        by (subst HOLD; lia).
      rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
  rewrite !Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 8) with 256 by reflexivity.
  replace (2 ^ 24) with 16777216 by reflexivity.
  lia.
Qed.

(** The CHECK arm on the four big-endian adler bytes, falling through
    LENGTH into DONE: the running check (folded over the whole output —
    or the seed itself when nothing was written) matches the trailer and
    the machine leaves with Z_STREAM_END. *)
Lemma zr_step_check : forall AD tot chk z stream nxt obuf put cap,
  0 <= AD < 4294967296 ->
  0 <= put ->
  zlist stream nxt = u8 (AD / 16777216) ->
  zlist stream (nxt + 1) = u8 (AD / 65536) ->
  zlist stream (nxt + 2) = u8 (AD / 256) ->
  zlist stream (nxt + 3) = u8 AD ->
  4 <= zlen stream - nxt ->
  (put = 0 -> chk = AD) ->
  (0 < put ->
     adler32_z chk false
       (ob_slice {| o_buf := obuf; o_put := put; o_left := cap - put |} 0 put)
     = AD) ->
  exists q',
    inf_step zr_ic (zrq (zr_ist M_CHECK 1 0 tot chk) z stream nxt obuf put cap)
    = InfLeave q'
    /\ q_ret q' = Z_STREAM_END
    /\ q_ob q' = {| o_buf := obuf; o_put := put; o_left := cap - put |}
    /\ q_in q' = zlen stream
    /\ q_out q' = cap - put
    /\ h_mode (s_hdr (q_st q')) = M_DONE
    /\ w_wsize (s_win (q_st q')) = 0.
Proof.
  intros AD tot chk z stream nxt obuf put cap
         HAD Hput Hb0 Hb1 Hb2 Hb3 Hin Hck0 Hckp.
  unfold inf_step.
  replace (q_mode (zrq (zr_ist M_CHECK 1 0 tot chk) z stream nxt obuf put cap))
    with M_CHECK by reflexivity.
  unfold inf_CHECK. cbv zeta.
  unfold zrq. cbn [q_st q_br q_ob q_out].
  replace (h_wrap (s_hdr (zr_ist M_CHECK 1 0 tot chk))) with 5 by reflexivity.
  replace (5 =? 0) with false by reflexivity.
  rewrite inf_nb_pull4 by lia.
  rewrite Hb0, Hb1, Hb2, Hb3.
  cbn [o_left o_put o_buf].
  replace (cap - (cap - put)) with put by lia.
  replace (Z.land 5 4) with 4 by reflexivity.
  replace (4 =? 0) with false by reflexivity.
  cbn [negb andb].
  replace (h_flags (s_hdr (zr_ist M_CHECK 1 0 tot chk))) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  destruct (put =? 0) eqn:EP.
  - (* nothing written: the seed is the trailer value *)
    apply Z.eqb_eq in EP.
    rewrite (Hck0 EP).
    cbn [negb andb].
    unfold qset_out, qset_st, qset_z, qset_br, qmode, qcheck, qset_ret,
           br_initbits.
    cbn [q_st q_z q_br q_ob q_in q_out q_ret
         br_in br_have br_next br_hold br_bits s_hdr h_check h_total
         o_left o_put o_buf].
    rewrite zr_zswap32_be by lia.
    match goal with
    | |- context [AD =? ?CK] => replace CK with AD by reflexivity
    end.
    replace (AD =? AD) with true by (symmetry; apply Z.eqb_refl).
    cbn [negb andb].
    unfold inf_LENGTH.
    match goal with
    | |- context [h_wrap ?T =? 0] =>
        replace (h_wrap T) with 5 by reflexivity
    end.
    replace (5 =? 0) with false by reflexivity.
    match goal with
    | |- context [h_flags ?T =? 0] =>
        replace (h_flags T) with 0 by reflexivity
    end.
    replace (0 =? 0) with true by reflexivity.
    cbn [negb andb].
    unfold inf_DONE, qmode, qset_st, qset_ret.
    cbn [q_st q_z q_br q_ob q_in q_out q_ret].
    eexists. split; [reflexivity|].
    repeat split; reflexivity.
  - (* output written: the folded check is the trailer value *)
    apply Z.eqb_neq in EP.
    cbn [negb andb].
    unfold upd_check.
    replace (h_flags (s_hdr (zr_ist M_CHECK 1 0 tot chk))) with 0
      by reflexivity.
    replace (0 =? 0) with true by reflexivity.
    replace (put - put) with 0 by lia.
    replace (h_check (s_hdr (zr_ist M_CHECK 1 0 tot chk))) with chk
      by reflexivity.
    rewrite (Hckp ltac:(lia)).
    unfold qset_out, qset_st, qset_z, qset_br, qmode, qcheck, qset_ret,
           br_initbits.
    cbn [q_st q_z q_br q_ob q_in q_out q_ret
         br_in br_have br_next br_hold br_bits s_hdr h_check h_total
         o_left o_put o_buf].
    rewrite zr_zswap32_be by lia.
    match goal with
    | |- context [AD =? ?CK] => replace CK with AD by reflexivity
    end.
    replace (AD =? AD) with true by (symmetry; apply Z.eqb_refl).
    cbn [negb andb].
    unfold inf_LENGTH.
    match goal with
    | |- context [h_wrap ?T =? 0] =>
        replace (h_wrap T) with 5 by reflexivity
    end.
    replace (5 =? 0) with false by reflexivity.
    match goal with
    | |- context [h_flags ?T =? 0] =>
        replace (h_flags T) with 0 by reflexivity
    end.
    replace (0 =? 0) with true by reflexivity.
    cbn [negb andb].
    unfold inf_DONE, qmode, qset_st, qset_ret.
    cbn [q_st q_z q_br q_ob q_in q_out q_ret].
    eexists. split; [reflexivity|].
    repeat split; reflexivity.
Qed.

(** [inf_leave] at the DONE exit with the write-snapshot already reset:
    the no-window branch, no double check-fold, and Z_BUF_ERROR cannot
    fire on a Z_STREAM_END return. *)
Lemma zr_leave_done : forall q',
  q_ret q' = Z_STREAM_END ->
  q_out q' = o_left (q_ob q') ->
  h_mode (s_hdr (q_st q')) = M_DONE ->
  w_wsize (s_win (q_st q')) = 0 ->
  snd (inf_leave zr_ic q') = Z_STREAM_END
  /\ q_ob (fst (inf_leave zr_ic q')) = q_ob q'.
Proof.
  (* cure (walks-a0, 2026-09-08; TL commission on the j6 OOM): the setter chain of inf_leave_tail is never UNFOLDED — the old
     `unfold qset_ret, qset_out, qset_in, qset_z, qset_st, qcheck` materialised each setter as a 7-field record under six
     nested lets (~7^6 copies of the state) before the projections reduced (21 s + 23 s Qed, ~4.9 GiB).  Here the state is
     first frozen as an opaque local (set + clearbody), the lets are inlined over that VARIABLE, and the projections reduce
     through the folded setters lazily with cbn.  Statement byte-identical. *)
  intros q' Hret Hout Hmode Hw.
  unfold inf_leave.
  set (q := q_restore q').
  assert (Hw' : w_wsize (s_win (q_st q)) = 0) by exact Hw.
  assert (Hout' : q_out q = o_left (q_ob q)) by exact Hout.
  assert (Hret' : q_ret q = Z_STREAM_END) by exact Hret.
  assert (Hob : q_ob q = q_ob q') by reflexivity.
  clearbody q.
  cbv zeta.
  rewrite Hw'.
  replace (0 =? 0) with true by reflexivity.
  cbn [negb].
  rewrite Hout'.
  replace (o_left (q_ob q) =? o_left (q_ob q)) with true
    by (symmetry; apply Z.eqb_refl).
  cbn [negb andb orb].
  unfold inf_leave_tail. cbv zeta.
  cbn [qset_ret qset_out qset_in qset_z qset_st qcheck
       q_st q_z q_br q_ob q_in q_out q_ret fst snd].
  replace (o_left (q_ob q) - o_left (q_ob q)) with 0 by lia.
  replace (0 =? 0) with true by reflexivity.
  replace (n_flush zr_ic =? Z_FINISH) with true by reflexivity.
  rewrite ?andb_true_r, ?orb_true_r, ?andb_false_r.
  cbn [negb andb qset_ret qset_out qset_in qset_z qset_st qcheck q_ret q_ob fst snd].
  rewrite Hret'.
  replace (Z_STREAM_END =? Z_OK) with false by reflexivity.
  cbn [andb fst snd qset_ret qset_out qset_in qset_z qset_st qcheck q_ob q_ret].
  split; [reflexivity|].
  exact Hob.
Qed.

(** Loop plumbing. *)
Lemma inf_loop_cont : forall n c q q',
  inf_step c q = InfCont q' ->
  inf_loop (S n) c q = inf_loop n c q'.
Proof. intros n c q q' H. cbn [inf_loop]. now rewrite H. Qed.

Lemma inf_loop_leave : forall n c q q',
  inf_step c q = InfLeave q' ->
  inf_loop (S n) c q = Some (InfLeave q').
Proof. intros n c q q' H. cbn [inf_loop]. now rewrite H. Qed.

Lemma inf_loop_grow : forall n m c q r,
  inf_loop n c q = Some (InfLeave r) ->
  (n <= m)%nat ->
  inf_loop m c q = Some (InfLeave r).
Proof.
  induction n as [|n IH]; intros m c q r H Hle; [discriminate|].
  destruct m as [|m]; [lia|].
  cbn [inf_loop] in H |- *.
  destruct (inf_step c q) as [q1|q1|q1 r1|m1|] eqn:E; try exact H.
  apply IH; [exact H | lia].
Qed.

(** Positional reads through the stream decomposition. *)
Lemma zlist_app_r : forall (l1 l2 : list Z) i,
  0 <= i ->
  zlist (l1 ++ l2) (zlen l1 + i) = zlist l2 i.
Proof.
  intros l1 l2 i Hi. unfold zlist, zlen.
  replace (Z.to_nat (Z.of_nat (length l1) + i))
    with (length l1 + Z.to_nat i)%nat by lia.
  apply app_nth2_plus.
Qed.

Lemma zlist_cons_0 : forall (a : Z) (l : list Z), zlist (a :: l) 0 = a.
Proof. reflexivity. Qed.

Lemma zlist_cons_S : forall (a : Z) (l : list Z) i,
  0 <= i -> zlist (a :: l) (1 + i) = zlist l i.
Proof.
  intros a l i Hi. unfold zlist.
  replace (Z.to_nat (1 + i)) with (S (Z.to_nat i)) by lia.
  reflexivity.
Qed.

Lemma zlen_map_u8 : forall (l : list Z), zlen (map u8 l) = zlen l.
Proof. intro l. unfold zlen. now rewrite length_map. Qed.

Lemma zlist_map_u8 : forall (l : list Z) i,
  0 <= i < zlen l -> zlist (map u8 l) i = u8 (zlist l i).
Proof.
  intros l i Hi. unfold zlist, zlen in *.
  rewrite (nth_indep (map u8 l) 0 (u8 0)) by (rewrite length_map; lia).
  apply map_nth.
Qed.

Lemma zlen_hdr : forall last len, zlen (zr_stored_hdr last len) = 5.
Proof. reflexivity. Qed.

Lemma zlist_app_l : forall (l1 l2 : list Z) i,
  0 <= i < zlen l1 ->
  zlist (l1 ++ l2) i = zlist l1 i.
Proof.
  intros l1 l2 i Hi. unfold zlist, zlen in *.
  apply app_nth1. lia.
Qed.

Lemma zlist_firstn : forall (l : list Z) n i,
  0 <= i < n -> zlist (firstn (Z.to_nat n) l) i = zlist l i.
Proof.
  intros l n i Hi. unfold zlist.
  rewrite nth_firstn.
  replace (Z.to_nat i <? Z.to_nat n)%nat with true
    by (symmetry; apply Nat.ltb_lt; lia).
  reflexivity.
Qed.

Lemma zlist_skipn : forall (l : list Z) n i,
  0 <= i -> 0 <= n -> zlist (skipn (Z.to_nat n) l) i = zlist l (n + i).
Proof.
  intros l n i Hi Hn. unfold zlist.
  rewrite nth_skipn.
  replace (Z.to_nat n + Z.to_nat i)%nat with (Z.to_nat (n + i)) by lia.
  reflexivity.
Qed.

(** THE WALK: from a TYPE entry with the remaining payload's stored-block
    serialization at the read position, the machine consumes exactly that
    serialization, emits exactly [map u8] of the payload, and returns to
    TYPE with BFINAL set — at most three trips per block. *)
Lemma zr_walk : forall bfuel (xrem : list Z) pre post chk z obuf put cap,
  (zr_body_fuel xrem <= bfuel)%nat ->
  zlen xrem <= cap - put ->
  0 <= put ->
  exists (k : nat) obuf',
    (k <= 3 * zr_body_fuel xrem)%nat
    /\ (forall n,
       inf_loop (k + n) zr_ic
         (zrq (zr_ist M_TYPE 0 0 0 chk) z
              (pre ++ zr_stored_body (zr_body_fuel xrem) xrem ++ post)
              (zlen pre) obuf put cap)
       = inf_loop n zr_ic
           (zrq (zr_ist M_TYPE 1 0 0 chk) z
                (pre ++ zr_stored_body (zr_body_fuel xrem) xrem ++ post)
                (zlen pre + zlen (zr_stored_body (zr_body_fuel xrem) xrem))
                obuf' (put + zlen xrem) cap))
    /\ (forall i, 0 <= i < put -> obuf' i = obuf i)
    /\ (forall i, 0 <= i < zlen xrem -> obuf' (put + i) = u8 (zlist xrem i)).
Proof.
  induction bfuel as [|bfuel IH];
    intros xrem pre post chk z obuf put cap Hf Hcap Hput.
  { unfold zr_body_fuel in Hf. lia. }
  pose proof (zlen_nonneg xrem) as Hxr.
  pose proof (zlen_nonneg pre) as Hpre.
  pose proof (zlen_nonneg post) as Hpost.
  destruct (Z.leb (zlen xrem) 65535) eqn:E65b.
  - (* the final block *)
    pose proof E65b as E65B.
    apply Z.leb_le in E65b.
    assert (EB : zr_stored_body (zr_body_fuel xrem) xrem
                 = zr_stored_hdr 1 (zlen xrem) ++ map u8 xrem)
      by (unfold zr_body_fuel; cbn [zr_stored_body]; now rewrite E65B).
    rewrite !EB.
    set (BODY := zr_stored_hdr 1 (zlen xrem) ++ map u8 xrem) in *.
    set (STREAM := pre ++ BODY ++ post) in *.
    assert (HSr : forall i, 0 <= i ->
              zlist STREAM (zlen pre + i) = zlist (BODY ++ post) i).
    { intros i Hi. subst STREAM. now rewrite zlist_app_r by lia. }
    assert (HB : BODY ++ post
                 = 1 :: u8 (zlen xrem) :: u8 (Z.shiftr (zlen xrem) 8)
                   :: u8 (Z.lnot (zlen xrem))
                   :: u8 (Z.shiftr (u32 (Z.lnot (zlen xrem))) 8)
                   :: (map u8 xrem ++ post)).
    { subst BODY. unfold zr_stored_hdr. now rewrite <- app_assoc. }
    assert (F0 : zlist STREAM (zlen pre) = 1).
    { replace (zlen pre) with (zlen pre + 0) by lia.
      rewrite HSr by lia. rewrite HB. apply zlist_cons_0. }
    assert (F1 : zlist STREAM (zlen pre + 1) = u8 (zlen xrem)).
    { rewrite HSr by lia. rewrite HB.
      replace 1 with (1 + 0) by lia.
      rewrite zlist_cons_S by lia. apply zlist_cons_0. }
    assert (F2 : zlist STREAM (zlen pre + 1 + 1) = u8 (Z.shiftr (zlen xrem) 8)).
    { replace (zlen pre + 1 + 1) with (zlen pre + 2) by lia.
      rewrite HSr by lia. rewrite HB.
      replace 2 with (1 + (1 + 0)) by lia.
      rewrite !zlist_cons_S by lia. apply zlist_cons_0. }
    assert (F3 : zlist STREAM (zlen pre + 1 + 2) = u8 (Z.lnot (zlen xrem))).
    { replace (zlen pre + 1 + 2) with (zlen pre + 3) by lia.
      rewrite HSr by lia. rewrite HB.
      replace 3 with (1 + (1 + (1 + 0))) by lia.
      rewrite !zlist_cons_S by lia. apply zlist_cons_0. }
    assert (F4 : zlist STREAM (zlen pre + 1 + 3)
                 = u8 (Z.shiftr (u32 (Z.lnot (zlen xrem))) 8)).
    { replace (zlen pre + 1 + 3) with (zlen pre + 4) by lia.
      rewrite HSr by lia. rewrite HB.
      replace 4 with (1 + (1 + (1 + (1 + 0)))) by lia.
      rewrite !zlist_cons_S by lia. apply zlist_cons_0. }
    assert (FP : forall i, 0 <= i < zlen xrem ->
              zlist STREAM (zlen pre + 5 + i) = u8 (zlist xrem i)).
    { intros i Hi.
      replace (zlen pre + 5 + i) with (zlen pre + (5 + i)) by lia.
      rewrite HSr by lia. rewrite HB.
      replace (5 + i) with (1 + (1 + (1 + (1 + (1 + i))))) by lia.
      rewrite !zlist_cons_S by lia.
      rewrite zlist_app_l by (rewrite zlen_map_u8; lia).
      now apply zlist_map_u8. }
    assert (HLS : zlen STREAM = zlen pre + 5 + zlen xrem + zlen post).
    { subst STREAM BODY.
      rewrite !zlen_app, zlen_hdr, zlen_map_u8. lia. }
    assert (HLB : zlen BODY = 5 + zlen xrem).
    { subst BODY. rewrite zlen_app, zlen_hdr, zlen_map_u8. lia. }
    destruct (Z.eqb (zlen xrem) 0) eqn:E0b.
    + (* empty final block *)
      apply Z.eqb_eq in E0b.
      assert (Exr : xrem = []) by (apply zlen_nil; lia).
      exists 2%nat, obuf.
      split; [unfold zr_body_fuel; lia|].
      split; [|split; [intros; reflexivity | intros; lia]].
      intro n.
      replace (2 + n)%nat with (S (S n)) by lia.
      rewrite (inf_loop_cont _ _ _ _
        (zr_step_type 1 0 0 chk z STREAM (zlen pre) obuf put cap
           ltac:(lia) F0 ltac:(lia))).
      rewrite (inf_loop_cont _ _ _ _
        (zr_step_stored0 1 0 chk z STREAM (zlen pre + 1) obuf put cap
           ltac:(lia)
           ltac:(rewrite F1, E0b; reflexivity)
           ltac:(replace (zlen pre + 1 + 1) with (zlen pre + 1 + 1) by lia;
                 rewrite F2, E0b; reflexivity)
           ltac:(rewrite F3, E0b; reflexivity)
           ltac:(rewrite F4, E0b; reflexivity)
           ltac:(lia))).
      replace (zlen pre + zlen BODY) with (zlen pre + 1 + 4) by lia.
      replace (put + zlen xrem) with put by lia.
      reflexivity.
    + (* payload-carrying final block *)
      apply Z.eqb_neq in E0b.
      exists 3%nat,
        (zcopy (Z.to_nat (zlen xrem)) obuf put (zlist STREAM) (zlen pre + 1 + 4)).
      split; [unfold zr_body_fuel; lia|].
      split; [|split].
      * intro n.
        replace (3 + n)%nat with (S (S (S n))) by lia.
        rewrite (inf_loop_cont _ _ _ _
          (zr_step_type 1 0 0 chk z STREAM (zlen pre) obuf put cap
             ltac:(lia) F0 ltac:(lia))).
        rewrite (inf_loop_cont _ _ _ _
          (zr_step_stored 1 (zlen xrem) 0 chk z STREAM (zlen pre + 1)
             obuf put cap ltac:(lia) ltac:(lia) ltac:(lia)
             F1 F2 F3 F4 ltac:(lia) ltac:(lia))).
        rewrite (inf_loop_cont _ _ _ _
          (zr_step_copy0 1 0 chk z STREAM (zlen pre + 1 + 4 + zlen xrem)
             (zcopy (Z.to_nat (zlen xrem)) obuf put (zlist STREAM)
                    (zlen pre + 1 + 4))
             (put + zlen xrem) cap)).
        replace (zlen pre + zlen BODY) with (zlen pre + 1 + 4 + zlen xrem)
          by lia.
        reflexivity.
      * intros i Hi.
        apply zcopy_miss. intros m Hm. lia.
      * intros i Hi.
        replace (put + i) with (put + Z.of_nat (Z.to_nat i)) by lia.
        rewrite zcopy_hit by lia.
        replace (zlen pre + 1 + 4 + Z.of_nat (Z.to_nat i))
          with (zlen pre + 5 + i) by lia.
        now apply FP.
  - (* a full block, then the rest by induction *)
    apply Z.leb_gt in E65b.
    pose proof (body_fuel_step xrem E65b) as EBF.
    assert (EB : zr_stored_body (zr_body_fuel xrem) xrem
                 = zr_stored_hdr 0 65535 ++ map u8 (firstn (Z.to_nat 65535) xrem)
                   ++ zr_stored_body (zr_body_fuel (skipn (Z.to_nat 65535) xrem))
                        (skipn (Z.to_nat 65535) xrem)).
    { rewrite EBF. cbn [zr_stored_body].
      replace (zlen xrem <=? 65535) with false
        by (symmetry; apply Z.leb_gt; lia).
      reflexivity. }
    rewrite !EB.
    set (CHUNK := map u8 (firstn (Z.to_nat 65535) xrem)) in *.
    set (XR' := skipn (Z.to_nat 65535) xrem) in *.
    set (BODY' := zr_stored_body (zr_body_fuel XR') XR') in *.
    pose proof (zlen_skipn_65535 xrem E65b) as HXR'.
    fold XR' in HXR'.
    assert (HCH : zlen CHUNK = 65535).
    { subst CHUNK. rewrite zlen_map_u8. unfold zlen.
      rewrite length_firstn. unfold zlen in Hxr, E65b |- *. lia. }
    set (STREAM := pre ++ (zr_stored_hdr 0 65535 ++ CHUNK ++ BODY') ++ post)
      in *.
    assert (ESTREAM : STREAM
              = (pre ++ zr_stored_hdr 0 65535 ++ CHUNK) ++ BODY' ++ post).
    { subst STREAM. now rewrite <- !app_assoc. }
    assert (HSr : forall i, 0 <= i ->
              zlist STREAM (zlen pre + i)
              = zlist ((zr_stored_hdr 0 65535 ++ CHUNK ++ BODY') ++ post) i).
    { intros i Hi. subst STREAM. now rewrite zlist_app_r by lia. }
    assert (HB : (zr_stored_hdr 0 65535 ++ CHUNK ++ BODY') ++ post
                 = 0 :: u8 65535 :: u8 (Z.shiftr 65535 8)
                   :: u8 (Z.lnot 65535)
                   :: u8 (Z.shiftr (u32 (Z.lnot 65535)) 8)
                   :: (CHUNK ++ BODY' ++ post)).
    { unfold zr_stored_hdr. now rewrite <- !app_assoc. }
    assert (F0 : zlist STREAM (zlen pre) = 0).
    { replace (zlen pre) with (zlen pre + 0) by lia.
      rewrite HSr by lia. rewrite HB. apply zlist_cons_0. }
    assert (F1 : zlist STREAM (zlen pre + 1) = u8 65535).
    { rewrite HSr by lia. rewrite HB.
      replace 1 with (1 + 0) by lia.
      rewrite zlist_cons_S by lia. apply zlist_cons_0. }
    assert (F2 : zlist STREAM (zlen pre + 1 + 1) = u8 (Z.shiftr 65535 8)).
    { replace (zlen pre + 1 + 1) with (zlen pre + 2) by lia.
      rewrite HSr by lia. rewrite HB.
      replace 2 with (1 + (1 + 0)) by lia.
      rewrite !zlist_cons_S by lia. apply zlist_cons_0. }
    assert (F3 : zlist STREAM (zlen pre + 1 + 2) = u8 (Z.lnot 65535)).
    { replace (zlen pre + 1 + 2) with (zlen pre + 3) by lia.
      rewrite HSr by lia. rewrite HB.
      replace 3 with (1 + (1 + (1 + 0))) by lia.
      rewrite !zlist_cons_S by lia. apply zlist_cons_0. }
    assert (F4 : zlist STREAM (zlen pre + 1 + 3)
                 = u8 (Z.shiftr (u32 (Z.lnot 65535)) 8)).
    { replace (zlen pre + 1 + 3) with (zlen pre + 4) by lia.
      rewrite HSr by lia. rewrite HB.
      replace 4 with (1 + (1 + (1 + (1 + 0)))) by lia.
      rewrite !zlist_cons_S by lia. apply zlist_cons_0. }
    assert (FP : forall i, 0 <= i < 65535 ->
              zlist STREAM (zlen pre + 5 + i) = u8 (zlist xrem i)).
    { intros i Hi.
      replace (zlen pre + 5 + i) with (zlen pre + (5 + i)) by lia.
      rewrite HSr by lia. rewrite HB.
      replace (5 + i) with (1 + (1 + (1 + (1 + (1 + i))))) by lia.
      rewrite !zlist_cons_S by lia.
      rewrite zlist_app_l by lia.
      subst CHUNK.
      rewrite zlist_map_u8
        by (unfold zlen; rewrite length_firstn; unfold zlen in *; lia).
      now rewrite zlist_firstn by lia. }
    assert (HLS : zlen STREAM
                  = zlen pre + 5 + 65535 + zlen BODY' + zlen post).
    { subst STREAM. rewrite !zlen_app, zlen_hdr. lia. }
    assert (HLBODY : zlen (zr_stored_hdr 0 65535 ++ CHUNK ++ BODY')
                     = 5 + 65535 + zlen BODY').
    { rewrite !zlen_app, zlen_hdr. lia. }
    assert (HB'len : 0 <= zlen BODY') by apply zlen_nonneg.
    (* the three trips of this block *)
    destruct (IH XR' (pre ++ zr_stored_hdr 0 65535 ++ CHUNK) post chk z
                 (zcopy (Z.to_nat 65535) obuf put (zlist STREAM)
                        (zlen pre + 1 + 4))
                 (put + 65535) cap ltac:(lia) ltac:(lia) ltac:(lia))
      as [k' [obuf'' [Hk' [Hloop' [Hlow' Hhi']]]]].
    fold BODY' in Hloop'.
    assert (EPRE : zlen (pre ++ zr_stored_hdr 0 65535 ++ CHUNK)
                   = zlen pre + 5 + 65535).
    { rewrite !zlen_app, zlen_hdr. lia. }
    exists (3 + k')%nat, obuf''.
    split; [rewrite EBF; fold XR'; lia|].
    split; [|split].
    + intro n.
      replace (3 + k' + n)%nat with (S (S (S (k' + n)))) by lia.
      rewrite (inf_loop_cont _ _ _ _
        (zr_step_type 0 0 0 chk z STREAM (zlen pre) obuf put cap
           ltac:(lia) F0 ltac:(lia))).
      rewrite (inf_loop_cont _ _ _ _
        (zr_step_stored 0 65535 0 chk z STREAM (zlen pre + 1)
           obuf put cap ltac:(lia) ltac:(lia) ltac:(lia)
           F1 F2 F3 F4 ltac:(lia) ltac:(lia))).
      rewrite (inf_loop_cont _ _ _ _
        (zr_step_copy0 0 0 chk z STREAM (zlen pre + 1 + 4 + 65535)
           (zcopy (Z.to_nat 65535) obuf put (zlist STREAM) (zlen pre + 1 + 4))
           (put + 65535) cap)).
      specialize (Hloop' n).
      rewrite ESTREAM.
      rewrite ESTREAM in Hloop'.
      replace (zlen pre + 1 + 4 + 65535)
        with (zlen (pre ++ zr_stored_hdr 0 65535 ++ CHUNK)) by lia.
      rewrite Hloop'.
      rewrite <- ESTREAM.
      replace (zlen (pre ++ zr_stored_hdr 0 65535 ++ CHUNK) + zlen BODY')
        with (zlen pre + zlen (zr_stored_hdr 0 65535 ++ CHUNK ++ BODY'))
        by lia.
      replace (put + 65535 + zlen XR') with (put + zlen xrem) by lia.
      reflexivity.
    + intros i Hi.
      rewrite Hlow' by lia.
      apply zcopy_miss. intros m Hm. lia.
    + intros i Hi.
      destruct (Z.ltb i 65535) eqn:EI.
      * apply Z.ltb_lt in EI.
        rewrite Hlow' by lia.
        replace (put + i) with (put + Z.of_nat (Z.to_nat i)) by lia.
        rewrite zcopy_hit by lia.
        replace (zlen pre + 1 + 4 + Z.of_nat (Z.to_nat i))
          with (zlen pre + 5 + i) by lia.
        now apply FP.
      * apply Z.ltb_ge in EI.
        replace (put + i) with ((put + 65535) + (i - 65535)) by lia.
        rewrite Hhi' by lia.
        subst XR'.
        rewrite zlist_skipn by lia.
        replace (65535 + (i - 65535)) with i by lia.
        reflexivity.
Qed.

(** The serialized body's length, and the slice-to-list bridge. *)
Lemma zlen_body : forall f (x : list Z),
  (zr_body_fuel x <= f)%nat ->
  zlen (zr_stored_body f x) = 5 * zr_nblocks x + zlen x.
Proof.
  induction f as [|f IH]; intros x Hf;
    [unfold zr_body_fuel in Hf; lia|].
  pose proof (zlen_nonneg x) as Hx.
  cbn [zr_stored_body].
  destruct (Z.leb (zlen x) 65535) eqn:E65.
  - apply Z.leb_le in E65.
    rewrite zlen_app, zlen_hdr, zlen_map_u8, nblocks_one by lia. lia.
  - apply Z.leb_gt in E65.
    pose proof (body_fuel_step x E65) as EBF.
    pose proof (nblocks_step x E65) as ENB.
    pose proof (zlen_skipn_65535 x E65) as EskL.
    rewrite !zlen_app, zlen_hdr, zlen_map_u8.
    rewrite IH by (unfold zr_body_fuel in *; lia).
    replace (zlen (firstn (Z.to_nat 65535) x)) with 65535.
    2:{ unfold zlen. rewrite length_firstn. unfold zlen in *. lia. }
    lia.
Qed.

Lemma zr_slice_is_map : forall (f : zarr) (x : list Z) L rest,
  zlen x = L ->
  (forall i, 0 <= i < L -> f i = u8 (zlist x i)) ->
  ob_slice {| o_buf := f; o_put := L; o_left := rest |} 0 L = map u8 x.
Proof.
  intros f x L rest HL Hpt.
  unfold ob_slice. cbn [o_buf].
  apply nth_error_ext. intro n.
  rewrite !nth_error_map, nth_error_seq.
  destruct (Nat.ltb n (Z.to_nat L)) eqn:EN.
  - apply Nat.ltb_lt in EN.
    replace (nth_error x n) with (Some (nth n x 0)).
    2:{ symmetry. apply nth_error_nth'. unfold zlen in HL. lia. }
    cbn [option_map].
    f_equal.
    replace (0 + Z.of_nat (0 + n)) with (Z.of_nat n) by lia.
    rewrite Hpt by lia.
    unfold zlist. now rewrite Nat2Z.id.
  - apply Nat.ltb_ge in EN.
    replace (nth_error x n) with (@None Z).
    2:{ symmetry. apply nth_error_None. unfold zlen in HL. lia. }
    reflexivity.
Qed.

Lemma zlen_be32 : forall v, zlen (be32 v) = 4.
Proof. reflexivity. Qed.

(** THE READ HALF: one-shot inflate at windowBits 15 maps the level-0
    stream back to the payload, byte-exactly, for any output cap that
    fits the payload. *)
Theorem zr_inflate_l0_stream : forall x cap,
  zlen x <= cap ->
  zr_inflate Z_FINISH 15 cap (zr_l0_stream x) = Some (map u8 x).
Proof.
  intros x cap Hcap.
  pose proof (zlen_nonneg x) as Hx.
  set (AD := adler32_z 1 false (map u8 x)).
  assert (HAV : AdVal AD).
  { subst AD.
    pose proof adval_init as HI.
    replace (adler32_z 0 true []) with 1 in HI by reflexivity.
    apply adval_step; [exact HI | apply ad_wf_map_u8]. }
  assert (HADb : 0 <= AD < 4294967296) by (destruct HAV as [_ ?]; assumption).
  assert (ESTREAM : zr_l0_stream x
            = [120; 1] ++ zr_stored_body (zr_body_fuel x) x ++ be32 AD).
  { unfold zr_l0_stream, AD.
    now replace (adler32_z 0 true []) with 1 by reflexivity. }
  set (BODY := zr_stored_body (zr_body_fuel x) x) in *.
  set (STREAM := [120; 1] ++ BODY ++ be32 AD) in *.
  pose proof (zlen_body (zr_body_fuel x) x ltac:(lia)) as HLB.
  fold BODY in HLB.
  pose proof (nblocks_pos x) as HNB.
  assert (HLS : zlen STREAM = 2 + zlen BODY + 4).
  { subst STREAM. rewrite !zlen_app, zlen_be32.
    replace (zlen [120; 1]) with 2 by reflexivity. lia. }
  unfold zr_inflate.
  rewrite zr_init_15.
  unfold zr_inf_call.
  rewrite ESTREAM. fold BODY. fold STREAM.
  unfold inflate_model.
  cbn [g_state_null g_out_null g_in_null g_avail_in orb andb negb].
  replace (inf_ctx
             {| g_st := zr_ist0; g_state_null := false; g_z := zr_z0;
                g_inbuf := zlist STREAM; g_next_in := 0;
                g_avail_in := zlen STREAM; g_in_null := false;
                g_outbuf := zzero; g_next_out := 0; g_avail_out := cap;
                g_out_null := false; g_flush := Z_FINISH; g_walloc := true;
                g_wfresh := zzero |})
    with zr_ic by reflexivity.
  assert (E0 : inf_st0
             {| g_st := zr_ist0; g_state_null := false; g_z := zr_z0;
                g_inbuf := zlist STREAM; g_next_in := 0;
                g_avail_in := zlen STREAM; g_in_null := false;
                g_outbuf := zzero; g_next_out := 0; g_avail_out := cap;
                g_out_null := false; g_flush := Z_FINISH; g_walloc := true;
                g_wfresh := zzero |}
             = zrq zr_ist0 zr_z0 STREAM 0 zzero 0 cap).
  { unfold inf_st0, zrq.
    cbn [g_st g_z g_inbuf g_avail_in g_next_in g_outbuf g_next_out
         g_avail_out g_flush].
    replace (h_mode (s_hdr zr_ist0)) with M_HEAD by reflexivity.
    cbn [s_hold s_bits].
    f_equal; f_equal; first [reflexivity | lia
                            | f_equal; first [reflexivity | lia]]. }
  rewrite E0.
  set (FUEL := Inflate.inf_fuel (zrq zr_ist0 zr_z0 STREAM 0 zzero 0 cap)) in *.
  assert (EF : FUEL
    = S (Z.to_nat (33 * (8 * (zlen STREAM - 0) + 0 + (cap - 0) + 1))))
    by reflexivity.
  set (F1 := Z.to_nat (33 * (8 * (zlen STREAM - 0) + 0 + (cap - 0) + 1)))
    in *.
  assert (Hdivle : zlen x / 65535 <= zlen x)
    by (apply Z.div_le_upper_bound; lia).
  assert (HFB : (3 * zr_body_fuel x + 3 <= F1)%nat)
    by (unfold zr_body_fuel; subst F1; lia).
  (* the head step *)
  destruct (zr_step_head zr_z0 (BODY ++ be32 AD) zzero cap) as [z1 Hhead].
  destruct (zr_walk (zr_body_fuel x) x [120; 1] (be32 AD) 1 z1 zzero 0 cap
              ltac:(lia) ltac:(lia) ltac:(lia))
    as [k [obuf' [Hk [Hloop [Hlow Hhi]]]]].
  fold BODY in Hloop.
  assert (ES2 : STREAM = 120 :: 1 :: (BODY ++ be32 AD))
    by (subst STREAM; reflexivity).
  assert (ES3 : forall t : list Z, [120; 1] ++ BODY ++ t = 120 :: 1 :: (BODY ++ t))
    by reflexivity.
  rewrite ES3 in Hloop.
  replace (zlen [120; 1]) with 2 in Hloop by reflexivity.
  rewrite EF, ES2.
  rewrite (inf_loop_cont _ _ _ _ Hhead).
  replace F1 with (k + (F1 - k))%nat by lia.
  rewrite Hloop.
  replace (F1 - k)%nat with (S (S (F1 - k - 2)))%nat by lia.
  rewrite (inf_loop_cont _ _ _ _
    (zr_step_type_final 0 0 1 z1 (120 :: 1 :: (BODY ++ be32 AD))
       (2 + zlen BODY) obuf' (0 + zlen x) cap)).
  (* the trailer bytes *)
  assert (ES4 : (120 :: 1 :: (BODY ++ be32 AD))
                = ([120; 1] ++ BODY) ++ be32 AD)
    by reflexivity.
  assert (HL2 : zlen ([120; 1] ++ BODY) = 2 + zlen BODY)
    by (rewrite zlen_app; now replace (zlen [120; 1]) with 2 by reflexivity).
  assert (FT : forall j, 0 <= j ->
            zlist (120 :: 1 :: (BODY ++ be32 AD)) (2 + zlen BODY + j)
            = zlist (be32 AD) j).
  { intros j Hj. rewrite ES4.
    replace (2 + zlen BODY + j) with (zlen ([120; 1] ++ BODY) + j) by lia.
    now rewrite zlist_app_r by lia. }
  assert (FT0 : zlist (120 :: 1 :: (BODY ++ be32 AD)) (2 + zlen BODY)
                = u8 (AD / 16777216)).
  { replace (2 + zlen BODY) with (2 + zlen BODY + 0) by lia.
    rewrite FT by lia. reflexivity. }
  assert (FT1 : zlist (120 :: 1 :: (BODY ++ be32 AD)) (2 + zlen BODY + 1)
                = u8 (AD / 65536)).
  { rewrite FT by lia. reflexivity. }
  assert (FT2 : zlist (120 :: 1 :: (BODY ++ be32 AD)) (2 + zlen BODY + 2)
                = u8 (AD / 256)).
  { rewrite FT by lia. reflexivity. }
  assert (FT3 : zlist (120 :: 1 :: (BODY ++ be32 AD)) (2 + zlen BODY + 3)
                = u8 AD).
  { rewrite FT by lia. reflexivity. }
  assert (HL3 : zlen (120 :: 1 :: (BODY ++ be32 AD)) = 2 + zlen BODY + 4).
  { rewrite !zlen_cons, zlen_app, zlen_be32. lia. }
  assert (HCK0 : 0 + zlen x = 0 -> 1 = AD).
  { intro HP0.
    assert (Exnil : x = []) by (apply zlen_nil; lia).
    unfold AD. rewrite Exnil. reflexivity. }
  assert (HCKP : 0 < 0 + zlen x ->
    adler32_z 1 false
      (ob_slice {| o_buf := obuf'; o_put := 0 + zlen x;
                   o_left := cap - (0 + zlen x) |} 0 (0 + zlen x))
    = AD).
  { intro HPp.
    rewrite (zr_slice_is_map obuf' x (0 + zlen x) (cap - (0 + zlen x))
               ltac:(lia)
               ltac:(intros i Hi; replace i with (0 + i) by lia;
                     apply Hhi; lia)).
    unfold AD. reflexivity. }
  destruct (zr_step_check AD 0 1 z1 (120 :: 1 :: (BODY ++ be32 AD))
              (2 + zlen BODY) obuf' (0 + zlen x) cap
              HADb ltac:(lia) FT0 FT1 FT2 FT3 ltac:(lia) HCK0 HCKP)
    as [q' [Hstep [Hret [Hob [Hin [Hout [Hmode Hw]]]]]]].
  rewrite (inf_loop_leave _ _ _ _ Hstep).
  destruct (zr_leave_done q' Hret ltac:(rewrite Hout, Hob; reflexivity)
              Hmode Hw) as [Hsnd Hfst].
  rewrite (surjective_pairing (inf_leave zr_ic q')).
  cbn [r_ret r_q].
  rewrite Hsnd, Hfst, Hob.
  cbn [o_put o_left o_buf].
  replace (Z_STREAM_END =? Z_STREAM_END) with true by reflexivity.
  f_equal.
  apply (zr_slice_is_map obuf' x (0 + zlen x) (cap - (0 + zlen x))
           ltac:(lia)).
  intros i Hi.
  replace i with (0 + i) by lia.
  apply Hhi. lia.
Qed.

(* ==========================================================================
   THE (0, 15) CONJUNCT — Q2's deliverable.
   ========================================================================== *)

Lemma map_u8_id : forall (x : list Z),
  Forall (fun b => 0 <= b < 256) x -> map u8 x = x.
Proof.
  intros x H. induction H as [|a l Ha Hl IH]; [reflexivity|].
  cbn [map]. rewrite IH. now rewrite u8_id by lia.
Qed.

(** The config (0, 15) round trip, hypothesis-free at the harness's exact
    call shape: proved DIRECTLY (emitter shape theorem + one-shot inflate
    walk), not through the shared zlib inflater face — closing that face
    in general is the full Huffman (b) and is not needed for this
    conjunct. *)
Theorem ZRepro_RoundTrip_l0_zlib_holds : ZRepro_RoundTrip_l0_zlib.
Proof.
  unfold ZRepro_RoundTrip_l0_zlib, ZR_RoundTrip.
  intros x [Hbytes Hcap].
  pose proof (zlen_nonneg x) as Hx.
  exists (zr_l0_stream x).
  split.
  - apply zr_deflate_l0_shape.
  - rewrite (zr_inflate_l0_stream x (zlen x + 1) ltac:(lia)).
    f_equal. now apply map_u8_id.
Qed.

(** And the same identity at the compress-path cap (avail_out = len
    exactly): the walk never needed the spare byte. *)
Theorem zr_l0_roundtrip_tight_cap : forall x,
  ZR_Input x ->
  exists enc, zr_deflate 0 15 x = Some enc
           /\ zr_inflate Z_FINISH 15 (zlen x) enc = Some x.
Proof.
  intros x [Hbytes Hcap].
  pose proof (zlen_nonneg x) as Hx.
  exists (zr_l0_stream x).
  split.
  - apply zr_deflate_l0_shape.
  - rewrite (zr_inflate_l0_stream x (zlen x) ltac:(lia)).
    f_equal. now apply map_u8_id.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Locate ZRepro_RoundTrip_l0_zlib_holds.
Print Assumptions ZRepro_RoundTrip_l0_zlib_holds.
Locate zr_inflate_l0_stream.
Print Assumptions zr_inflate_l0_stream.
Locate zr_walk.
Print Assumptions zr_walk.
