(** * Spec.PngModel.Inflate14 — zlib 1.4's [inflate] as the RT reference, beside 1.3.1's [Inflate]

    (option (A)).  1.4's [inflate.c] differs from 1.3.1's in three
    places of the mode machine that a lock-step bridge can see:
    - HEAD ([inflate.c] 1.4 l.548-554): the window-size check comes BEFORE [wbits] is set from the header, and a
      zero [wbits] is not compared ([len > 15 || (wbits != 0 && len > wbits)]); 1.3.1 stored [wbits = len] first;
    - LENLENS (l.820): [state->lencode = state->distcode = state->next], so distcode too points at the codes;
    - LEN (l.924): the [inflate_fast] path also needs [bits < 8].
    Every other arm is 1.3.1's word for word, so this file only adds twins of the arms that change and of those that
    fall through into them (TABLE -> LENLENS -> CODELENS -> LEN_ -> LEN), of the dispatch [inf_step14], of the
    loops [inf_iter14] / [inf_loop14], and of the entry [inflate_model14].  [Inflate] itself is untouched: png's
    chain and every 1.3.1 file keep their texts. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** [case LEN] at 1.4: [inf_LEN]'s text with the fast-path guard [have >= 6 && left >= 258 && bits < 8]. *)
Definition inf_LEN14 (q : InfSt) : InfStep :=
  let st := q_st q in
  let tb := s_tab st in
  let b  := q_br q in
  let o  := q_ob q in
  if Z.leb 6 (br_have b) && Z.leb 258 (o_left o) && Z.ltb (br_bits b) 8 then
    let q0 := q_restore q in
    match if_model {| a_inbuf     := br_in b;
                      a_next_in   := br_next b;
                      a_avail_in  := br_have b;
                      a_buf       := o_buf o;
                      a_next_out  := o_put o;
                      a_avail_out := o_left o;
                      a_start     := q_out q;
                      a_wsize     := w_wsize (s_win st);
                      a_whave     := w_whave (s_win st);
                      a_wnext     := w_wnext (s_win st);
                      a_window    := w_win (s_win st);
                      a_lcode     := tbl_of st (t_lencode tb);
                      a_dcode     := tbl_of st (t_distcode tb);
                      a_lenbits   := t_lenbits tb;
                      a_distbits  := t_distbits tb;
                      a_sane      := t_sane tb;
                      a_hold      := s_hold (q_st q0);
                      a_bits      := s_bits (q_st q0) |} with
    | None => InfFuel
    | Some y =>
        let st1 := set_bits (set_hold (q_st q0) (y_hold y)) (y_bits y) in
        let q1  := qset_st q0 st1 in
        let q2  := qset_br q1 {| br_in := br_in b; br_have := y_avail_in y;
                                 br_next := y_in y;
                                 br_hold := br_hold b; br_bits := br_bits b |} in
        let q3  := qset_ob q2 {| o_buf := y_buf y; o_put := y_out y;
                                 o_left := y_avail_out y |} in
        let q4  := match y_exit y with
                   | ExLen    => q3
                   | ExType   => qmode q3 M_TYPE
                   | ExBad m  => qbad q3 m
                   end in
        let q5 := q_load q4 in
        InfCont (match q_mode q5 with
                 | M_TYPE => qset_st q5 (set_back (q_st q5) (-1))
                 | _ => q5
                 end)
    end
  else
    let q0 := qset_st q (set_back st 0) in
    match inf_decode sub_len (tbl_of st (t_lencode tb)) (t_lenbits tb) b with
    | DecFuel      => InfFuel
    | DecLeave b'  => InfLeave (qset_br q0 b')
    | DecOk h b' nb =>
        let st1 := set_length (set_back (q_st q0) (0 + nb)) (c_val h) in
        let q1  := qset_br (qset_st q0 st1) b' in
        if Z.eqb (c_op h) 0 then
          InfCont (qmode q1 M_LIT)
        else if negb (Z.eqb (Z.land (c_op h) 32) 0) then
          InfCont (qmode (qset_st q1 (set_back (q_st q1) (-1))) M_TYPE)
        else if negb (Z.eqb (Z.land (c_op h) 64) 0) then
          InfCont (qbad q1 MSG_LIT_LEN_CODE)
        else
          let st2 := set_extra (q_st q1) (Z.land (c_op h) 15) in
          inf_LENEXT (qmode (qset_st q1 st2) M_LENEXT)
    end.

Definition inf_LEN_14 (q : InfSt) : InfStep := inf_LEN14 (qmode q M_LEN).

(** [case CODELENS] at 1.4: 1.3.1's text, falling through to the 1.4 LEN_. *)
Definition inf_CODELENS14 (c : InfCtx) (q : InfSt) : InfStep :=
  let st := q_st q in
  let bd := s_bld st in
  let tb := s_tab st in
  let tot := b_nlen bd + b_ndist bd in
  let put_cl (s : ClSt) : InfSt :=
    qset_br (qset_st q (set_lens (set_have st (cl_have s)) (cl_lens s)))
            (cl_br s) in
  match cl_loop (S (Z.to_nat tot)) (tbl_of st (t_lencode tb)) (t_lenbits tb)
                tot {| cl_have := b_have bd; cl_lens := b_lens bd;
                       cl_br := q_br q |} with
  | None             => InfFuel
  | Some ClFuel      => InfFuel
  | Some (ClCont _)  => InfFuel
  | Some (ClLeave s) => InfLeave (put_cl s)
  | Some (ClBad s m) => InfCont (qbad (put_cl s) m)
  | Some (ClDone s) =>
      let q1 := put_cl s in
      let st1 := q_st q1 in
      if Z.eqb (cl_lens s 256) 0 then
        InfCont (qbad q1 MSG_NO_EOB)
      else
        match inf_table st1 CT_LENS (cl_lens s) (b_nlen bd) 9 0 with
        | None => InfFuel
        | Some (rl, bl, nx, cd) =>
            let st2 := set_codes (set_next (set_lenbits
                          (set_lencode st1 (TRcodes 0)) bl) nx) cd in
            let q2 := qset_ret (qset_st q1 st2) rl in
            if negb (Z.eqb rl 0) then InfCont (qbad q2 MSG_LIT_LEN_SET)
            else
              match inf_table st2 CT_DISTS
                      (fun i => cl_lens s (i + b_nlen bd)) (b_ndist bd) 6 nx with
              | None => InfFuel
              | Some (rd, bdst, nx2, cd2) =>
                  let st3 := set_codes (set_next (set_distbits
                                (set_distcode st2 (TRcodes nx)) bdst) nx2) cd2 in
                  let q3 := qset_ret (qset_st q2 st3) rd in
                  if negb (Z.eqb rd 0) then InfCont (qbad q3 MSG_DIST_SET)
                  else if Z.eqb (n_flush c) Z_TREES then
                    InfLeave (qmode q3 M_LEN_)
                  else inf_LEN_14 (qmode q3 M_LEN_)
              end
        end
  end.

(** [case LENLENS] at 1.4: distcode is set with lencode (l.820), then 1.4's CODELENS. *)
Definition inf_LENLENS14 (c : InfCtx) (q : InfSt) : InfStep :=
  let st := q_st q in
  let bd := s_bld st in
  match ll_go 19 (b_ncode bd) (b_have bd) (b_lens bd) (q_br q) with
  | LlLeave hv ls b =>
      InfLeave (qset_br (qset_st q (set_lens (set_have st hv) ls)) b)
  | LlOk hv ls b =>
      let '(hv1, ls1) := ll_zero 19 hv ls in
      let st1 := set_lens (set_have st hv1) ls1 in
      match inf_table st1 CT_CODES ls1 19 7 0 with
      | None => InfFuel
      | Some (rc, bc, nx, cd) =>
          let st2 := set_codes (set_next (set_lenbits
                        (set_distcode (set_lencode st1 (TRcodes 0)) (TRcodes 0)) bc) nx) cd in
          let q1 := qset_ret (qset_br (qset_st q st2) b) rc in
          if negb (Z.eqb rc 0) then InfCont (qbad q1 MSG_CODE_LENGTHS)
          else inf_CODELENS14 c (qmode (qset_st q1 (set_have (q_st q1) 0))
                                       M_CODELENS)
      end
  end.

(** [case TABLE] at 1.4: 1.3.1's text, falling through to 1.4's LENLENS. *)
Definition inf_TABLE14 (c : InfCtx) (q : InfSt) : InfStep :=
  match inf_nb 14 (q_br q) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      let nlen  := br_bits_of 5 b + 257 in
      let b1    := br_dropbits 5 b in
      let ndist := br_bits_of 5 b1 + 1 in
      let b2    := br_dropbits 5 b1 in
      let ncode := br_bits_of 4 b2 + 4 in
      let b3    := br_dropbits 4 b2 in
      let st1   := set_ncode (set_ndist (set_nlen (q_st q) nlen) ndist) ncode in
      let q1    := qset_br (qset_st q st1) b3 in
      if Z.ltb 286 nlen || Z.ltb 30 ndist then InfCont (qbad q1 MSG_TOO_MANY)
      else inf_LENLENS14 c (qmode (qset_st q1 (set_have (q_st q1) 0)) M_LENLENS)
  end.

(** [case HEAD] at 1.4: the window-size check before the [wbits] store; a zero [wbits] is not compared. *)
Definition inf_HEAD14 (c : InfCtx) (q : InfSt) : InfStep :=
  let st := q_st q in
  let h  := s_hdr st in
  if Z.eqb (h_wrap h) 0 then
    inf_TYPEDO c (qmode q M_TYPEDO)
  else
    match inf_nb 16 (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        if negb (Z.eqb (Z.land (h_wrap h) 2) 0) && Z.eqb (br_hold b) 35615 then
          let st1 := if Z.eqb (w_wbits (s_win st)) 0 then set_wbits st 15 else st in
          let st2 := set_check st1 (crc32_z 0 true 0 []) in
          let ck  := crc32_z (h_check (s_hdr st2)) false 0
                             [Z.land (br_hold b) 255;
                              Z.land (Z.shiftr (br_hold b) 8) 255] in
          InfCont (qmode (qset_br (qset_st q (set_check st2 ck))
                                  (br_initbits b)) M_FLAGS)
        else if Z.eqb (Z.land (h_wrap h) 1) 0
                || negb (Z.eqb ((Z.shiftl (br_bits_of 8 b) 8
                                 + Z.shiftr (br_hold b) 8) mod 31) 0) then
          InfCont (qbad (qset_br q b) MSG_HEADER_CHECK)
        else if negb (Z.eqb (br_bits_of 4 b) Z_DEFLATED) then
          InfCont (qbad (qset_br q b) MSG_UNKNOWN_METHOD)
        else
          let b1  := br_dropbits 4 b in
          let len := br_bits_of 4 b1 + 8 in
          if Z.ltb 15 len
             || (negb (Z.eqb (w_wbits (s_win st)) 0) && Z.ltb (w_wbits (s_win st)) len) then
            InfCont (qbad (qset_br q b1) MSG_WINDOW_SIZE)
          else
            let st1 := if Z.eqb (w_wbits (s_win st)) 0 then set_wbits st len else st in
            let st2 := set_flags (set_dmax st1 (Z.shiftl 1 len)) 0 in
            let q1  := qcheck (qset_st q st2) (adler32_z 0 true []) in
            let m   := if Z.eqb (Z.land (br_hold b1) 512) 0 then M_TYPE else M_DICTID in
            let q2  := qset_br (qmode q1 m) (br_initbits b1) in
            InfCont q2
    end.

(** The 1.4 switch: [inf_step] with the six twins. *)
Definition inf_step14 (c : InfCtx) (q : InfSt) : InfStep :=
  match q_mode q with
  | M_HEAD     => inf_HEAD14 c q
  | M_FLAGS    => inf_FLAGS q
  | M_TIME     => inf_TIME q
  | M_OS       => inf_OS q
  | M_EXLEN    => inf_EXLEN q
  | M_EXTRA    => inf_EXTRA q
  | M_NAME     => inf_NAME q
  | M_COMMENT  => inf_COMMENT q
  | M_HCRC     => inf_HCRC q
  | M_DICTID   => inf_DICTID c q
  | M_DICT     => inf_DICT c q
  | M_TYPE     => inf_TYPE c q
  | M_TYPEDO   => inf_TYPEDO c q
  | M_STORED   => inf_STORED c q
  | M_COPY_    => inf_COPY_ q
  | M_COPY     => inf_COPY q
  | M_TABLE    => inf_TABLE14 c q
  | M_LENLENS  => inf_LENLENS14 c q
  | M_CODELENS => inf_CODELENS14 c q
  | M_LEN_     => inf_LEN_14 q
  | M_LEN      => inf_LEN14 q
  | M_LENEXT   => inf_LENEXT q
  | M_DIST     => inf_DIST q
  | M_DISTEXT  => inf_DISTEXT q
  | M_MATCH    => inf_MATCH q
  | M_LIT      => inf_LIT q
  | M_CHECK    => inf_CHECK q
  | M_LENGTH   => inf_LENGTH q
  | M_DONE     => inf_DONE q
  | M_BAD      => inf_BAD q
  | M_MEM      => inf_MEM q
  | M_SYNC     => inf_SYNC q
  end.

Fixpoint inf_iter14 (k : nat) (c : InfCtx) (q : InfSt) {struct k} : option InfSt :=
  match k with
  | O => Some q
  | S k' => match inf_step14 c q with
            | InfCont q' => inf_iter14 k' c q'
            | _ => None
            end
  end.

Fixpoint inf_loop14 (n : nat) (c : InfCtx) (q : InfSt) {struct n} : option InfStep :=
  match n with
  | O => None
  | S k => match inf_step14 c q with
           | InfCont q' => inf_loop14 k c q'
           | r => Some r
           end
  end.

Definition inflate_model14 (a : InfArgs) : option InfRes :=
  let q0 := inf_st0 a in
  if g_state_null a || g_out_null a
     || (g_in_null a && negb (Z.eqb (g_avail_in a) 0)) then
    Some {| r_ret := Z_STREAM_ERROR; r_q := q0 |}
  else
    let c := inf_ctx a in
    match inf_loop14 (inf_fuel q0) c q0 with
    | None              => None
    | Some InfFuel      => None
    | Some (InfDead _)  => None
    | Some (InfCont _)  => None
    | Some (InfRet q r) => Some {| r_ret := r; r_q := q |}
    | Some (InfLeave q) =>
        let '(q', r) := inf_leave c q in Some {| r_ret := r; r_q := q' |}
    end.

Lemma inf_iter14_S : forall k c q,
  inf_iter14 (S k) c q = match inf_step14 c q with
                         | InfCont q' => inf_iter14 k c q'
                         | _ => None
                         end.
Proof. reflexivity. Qed.

Lemma inf_loop14_S : forall n c q,
  inf_loop14 (S n) c q = match inf_step14 c q with
                         | InfCont q' => inf_loop14 n c q'
                         | r => Some r
                         end.
Proof. reflexivity. Qed.

(** The twins agree with 1.3.1 off the three changed arms, and on them where 1.4 behaves as 1.3.1. *)
Lemma inf_LEN14_low : forall q, br_bits (q_br q) < 8 -> inf_LEN14 q = inf_LEN q.
Proof.
  intros q H. unfold inf_LEN14, inf_LEN. cbv zeta.
  rewrite (proj2 (Z.ltb_lt _ _) H), andb_true_r. reflexivity.
Qed.

Lemma inf_step14_same : forall c q,
  q_mode q <> M_HEAD -> q_mode q <> M_TABLE -> q_mode q <> M_LENLENS -> q_mode q <> M_CODELENS ->
  q_mode q <> M_LEN_ -> q_mode q <> M_LEN ->
  inf_step14 c q = inf_step c q.
Proof.
  intros c q H1 H2 H3 H4 H5 H6. unfold inf_step14, inf_step.
  destruct (q_mode q); try reflexivity; congruence.
Qed.
