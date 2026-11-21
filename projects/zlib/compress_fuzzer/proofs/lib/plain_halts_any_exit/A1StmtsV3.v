(** * A1StmtsV3 — DYN ROUND Leg A1 statement set at WORKING TEXT v3
    (freeze doc v4 addendum, md5 75426016).  q7-decode, 2026-08-20.

    Supersedes the A1Stmts annex (, kept as the v2 record).
    Deltas from v2, all gate-2/verdict-driven plus four adjustments
    forced at proof-preparation time (reported to the chairs):

    GATE-DRIVEN (freeze v4):
      - child MARKER arm DROPPED (q6 C1 + g1 narrowing: no sub-table
        ever exists under an accepted incomplete code; complete codes
        populate every child slot).  zr_no_child_code retained below
        for the record only.
      - root MARKER arm guard = the EXACT RECORD [T i = mkCodeT 64 1 0]
        (q6 gate-2 (b): exact-64 true on-population, the 64-class
        fallback unsound off it; (c)+(d): val=0, bits=1 measured).
      - POPULATION BOUND as an explicit premise on ownership-consumer
        statements (q6's totalisation ruling): (length ll <= 286)%nat /
        (length dl <= 30)%nat.  Not consumed by the A-leg proofs (the
        ownership arms carry everything); it is the boundary-as-premise
        for the inhabitation side (g1 B3/B5) and rides here so the leg
        cannot be instantiated off-population.

    PROOF-PREP ADJUSTMENTS (A1 fork, reported):
      [ADJ-1] the root MARKER arm carries [root = 1] explicitly.  This
        is [M2]'s content made precise: the fetch stop at a marker
        buffers only c_bits = 1 real bit; the full root-window spelling
        (and hence hdecode-None) needs root <= br_bits, i.e. root = 1.
        Measured true (markers only occur at max==1 builds, where the
        builder shrinks root to 1); inhabitation: g1 B3 from the
        builder arithmetic root = min(root0, max).
      [ADJ-2] the chase statements carry the READER-ALIGNMENT
        implication (br_haligned b -> br_haligned b') in their Ok arms
        — folding GtBrAlign's zr_decode_align role into the chase, since
        the landed align lemma's sub-false premise is root-only by
        design and a separate two-level align lemma would duplicate the
        fetch inductions.
      [ADJ-3] the decode chase takes THREE sub-dispatch premises
        (leaf-sub-false from the ent pack, pointer-sub-true, marker-
        sub-false).  v2 dropped the root-only sub premise entirely, but
        the DISPATCH alignment (leaf selected, pointer chased, marker
        selected) is load-bearing at any table shape; all three are
        concrete lemmas at sub_len/sub_dist (pins + computation).
      [ADJ-4] the fetch chase's POINTER arm carries the pointer's
        children clause and width-covers directly (re-deriving them
        from ownership at the returned index is ambiguous: a slot could
        satisfy both leaf and pointer arms).

    GUARD NOTE: [mkCodeT 64 1 0] is the frozen guard (gate-2 (b)); no
    isolated swap point remains — a guard change now is a statement
    change, as the round ruled. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
(* FINAL-TRAIN RE-POINT (freeze v41): the ownership vocabulary landed in
   ItGWidth (zr_no_short_code / zr_no_long_code_at / zr_width_covers /
   zr_two_own_v3) and ItGClassHead (zr_ptr_children) — byte-identical
   modulo three annotation comments (diff-verified); the local
   duplicates are DELETED for these Requires.  Export so that downstream
   consumers (A1core..W5D, Composite) keep their unqualified spellings.
   zr_no_child_code stays local (retention of the withdrawn child-marker
   piece; not landed elsewhere). *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Export
  ItGWidth ItGClassHead.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Negative-ownership pieces.
   ========================================================================== *)

(** RETIRED at v3 (child marker arm dropped, freeze v4); retained for
    the record per the retention convention. *)
(* q6 landing-prep note (freeze v7): callers bound i < 2^root,
   op <= 15 - root; write_bits truncates out-of-range indices silently. *)
Definition zr_no_child_code (lens : list nat) (root i op j : Z) : Prop :=
  forall sym cw, code_for lens 15%nat sym = Some cw ->
    root < Z.of_nat (length cw) <= root + op ->
    firstn (length cw)
      (write_bits (Z.to_nat root) i ++ write_bits (Z.to_nat op) j) <> cw.

(* ==========================================================================
   2.  The ownership interface, WORKING TEXT v3.
   ========================================================================== *)

(* ==========================================================================
   3.  The negative-half consumer lemma (Huff has only the converse).
   ========================================================================== *)

Definition zr_hdecode_none_marker_STMT : Prop :=
  forall (A : Type) (table : list (list bool * A)) (bits : list bool),
    (forall cw a, In (cw, a) table -> is_prefix cw bits = false) ->
    hdecode table bits = None.

(* ==========================================================================
   4.  The chase theorem statements.
   ========================================================================== *)

Definition zr_fetch_hdecode_two_STMT : Prop :=
  forall (T : ztbl) (root : Z) (lens : list nat)
         (ent : nat -> Code) (b : BR),
    0 < root <= 15 ->
    ValidLengths lens 15%nat ->
    zr_two_own_v3 T root lens ent ->
    br_wf b ->
    match inf_fetch T root b with
    | FetchOk h b' =>
        br_stream b' = br_stream b
        /\ br_wf b'
        /\ (W2Stream.br_haligned b -> W2Stream.br_haligned b')
        /\ c_bits h <= br_bits b'
        /\ (  (* coded short *)
              (exists sym cw,
                 code_for lens 15%nat sym = Some cw
                 /\ h = ent sym
                 /\ c_bits h = Z.of_nat (length cw)
                 /\ hdecode (code_table lens 15%nat) (br_stream b')
                    = Some (sym, br_stream (br_dropbits (c_bits h) b')))
           \/ (* pointer: position + window + [ADJ-4] the arm's clauses *)
              (exists i, 0 <= i < 2 ^ root
                 /\ h = T i
                 /\ c_bits h = root
                 /\ 1 <= c_op h <= 15 - root
                 /\ 2 ^ root <= c_val h
                 /\ root <= br_bits b'
                 /\ firstn (Z.to_nat root) (br_stream b')
                    = write_bits (Z.to_nat root) i
                 /\ zr_width_covers lens root i (c_op h)
                 /\ zr_ptr_children T root lens ent i (c_op h) (c_val h))
           \/ (* marker *)
              (h = mkCodeT 64 1 0
                 /\ hdecode (code_table lens 15%nat) (br_stream b') = None))
    | FetchLeave b' => br_stream b' = br_stream b /\ br_wf b'
    | FetchFuel => True
    end.

Definition zr_decode_hdecode_two_STMT : Prop :=
  forall (sub : Code -> bool) (T : ztbl) (root : Z) (lens : list nat)
         (ent : nat -> Code) (b : BR),
    0 < root <= 15 ->
    ValidLengths lens 15%nat ->
    zr_two_own_v3 T root lens ent ->
    (* [ADJ-3] dispatch alignment, three concrete facts *)
    (forall sym cw, code_for lens 15%nat sym = Some cw ->
         sub (ent sym) = false) ->
    (forall e, c_op e <> 0 -> Z.land (c_op e) 240 = 0 -> sub e = true) ->
    sub (mkCodeT 64 1 0) = false ->
    br_wf b ->
    match inf_decode sub T root b with
    | DecOk h b' nb =>
        br_wf b'
        /\ (W2Stream.br_haligned b -> W2Stream.br_haligned b')
        /\ (  (* CODED, depth-invisible *)
              (exists sym cw,
                 code_for lens 15%nat sym = Some cw
                 /\ h = ent sym
                 /\ hdecode (code_table lens 15%nat) (br_stream b)
                    = Some (sym, br_stream b'))
           \/ (* MARKER: no spec parse; the consumer routes op=64 to BAD *)
              (h = mkCodeT 64 1 0
                 /\ hdecode (code_table lens 15%nat) (br_stream b) = None))
    | DecLeave b' => br_stream b' = br_stream b /\ br_wf b'
    | DecFuel => True
    end.

(* ==========================================================================
   5.  The trip seam statements (landed conclusions VERBATIM; premises:
       ownership v3 + pins + population bound; sub-false derived).
   ========================================================================== *)

Definition zr_len_split_two_STMT : Prop :=
  forall q (ll : list nat) (entl : nat -> Code),
  br_wf (q_br q) ->
  ValidLengths ll 15%nat ->
  zr_two_own_v3 (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll entl ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  zr_len_ents ll entl ->
  (length ll <= 286)%nat ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q))) = false ->
  inf_LEN q = InfFuel
  \/ (exists q2, inf_LEN q = InfLeave q2 /\ q_ret q2 = q_ret q)
  \/ (exists qb, inf_LEN q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  \/ (exists qL sym cw,
        inf_LEN q = InfCont qL
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, br_stream (q_br qL))
        /\ c_op (entl sym) = 0
        /\ u_length (s_cur (q_st qL)) = c_val (entl sym)
        /\ h_mode (s_hdr (q_st qL)) = M_LIT
        /\ br_wf (q_br qL)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qL))
        /\ zr_sframe q qL)
  \/ (exists qT sym cw,
        inf_LEN q = InfCont qT
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, br_stream (q_br qT))
        /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 <> 0
        /\ h_mode (s_hdr (q_st qT)) = M_TYPE
        /\ br_wf (q_br qT)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qT))
        /\ zr_sframe q qT)
  \/ (exists qE sym cw,
        inf_LEN q = inf_LENEXT qE
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, br_stream (q_br qE))
        /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 = 0
        /\ Z.land (c_op (entl sym)) 64 = 0
        /\ u_length (s_cur (q_st qE)) = c_val (entl sym)
        /\ u_extra (s_cur (q_st qE)) = Z.land (c_op (entl sym)) 15
        /\ br_wf (q_br qE)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qE))
        /\ zr_sframe q qE).

Definition zr_dist_split_two_STMT : Prop :=
  forall q (dl : list nat) (entd : nat -> Code),
  br_wf (q_br q) ->
  ValidLengths dl 15%nat ->
  zr_two_own_v3 (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl entd ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  zr_dist_ents dl entd ->
  (length dl <= 30)%nat ->
  inf_DIST q = InfFuel
  \/ (exists q2, inf_DIST q = InfLeave q2 /\ q_ret q2 = q_ret q)
  \/ (exists qb, inf_DIST q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  \/ (exists qX dsym cw,
        inf_DIST q = inf_DISTEXT qX
        /\ code_for dl 15%nat dsym = Some cw
        /\ hdecode (code_table dl 15%nat) (br_stream (q_br q))
           = Some (dsym, br_stream (q_br qX))
        /\ u_offset (s_cur (q_st qX)) = c_val (entd dsym)
        /\ u_extra (s_cur (q_st qX)) = Z.land (c_op (entd dsym)) 15
        /\ u_length (s_cur (q_st qX)) = u_length (s_cur (q_st q))
        /\ Z.land (c_op (entd dsym)) 64 = 0
        /\ br_wf (q_br qX)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qX))
        /\ zr_sframe q qX).

(* ==========================================================================
   6.  The trip twin statement: the landed zr_sym_trip with ownership v3,
       sub-false premises DROPPED (derived from the pins), population
       bounds added; conclusion VERBATIM.
   ========================================================================== *)

Definition zr_sym_trip_dyn_STMT : Prop :=
  forall c q (ll dl : list nat) (entl entd : nat -> Code),
  ValidLengths ll 15%nat ->
  ValidLengths dl 15%nat ->
  zr_two_own_v3 (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll entl ->
  zr_two_own_v3 (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl entd ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  zr_len_ents ll entl ->
  zr_dist_ents dl entd ->
  (length ll <= 286)%nat ->
  (length dl <= 30)%nat ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  h_mode (s_hdr (q_st q)) = M_LEN ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q))) = false ->
  (exists k q' sy,
     inf_iter k c q = Some q'
     /\ decode_lit_len ll dl (br_stream (q_br q))
        = Some (sy, br_stream (q_br q'))
     /\ match sy with
        | LzLit v =>
            ob_slice (q_ob q') 0 (o_put (q_ob q'))
            = ob_slice (q_ob q) 0 (o_put (q_ob q)) ++ [v]
            /\ h_mode (s_hdr (q_st q')) = M_LEN
        | LzEnd =>
            q_ob q' = q_ob q
            /\ h_mode (s_hdr (q_st q')) = M_TYPE
        | LzRef len dist =>
            (dist =? 0)%nat = false
            /\ Z.of_nat dist <= o_put (q_ob q)
            /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
               = ob_slice (q_ob q) 0 (o_put (q_ob q))
                 ++ lz_copy (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                            len dist
            /\ h_mode (s_hdr (q_st q')) = M_LEN
        end
     /\ br_wf (q_br q')
     /\ 0 <= o_put (q_ob q')
     /\ 0 <= o_left (q_ob q')
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ s_tab (q_st q') = s_tab (q_st q)
     /\ s_win (q_st q') = s_win (q_st q)
     /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br q'))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
     (* amendment #11: h_check/h_total frame conjuncts — carrier
        q7-decode; g1 census; q6 pre-ruling;
        #10 shape *)
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)))
  \/ (exists k q',
      inf_iter k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists n s,
      inf_loop n c q = Some s
      /\ match s with
         | InfLeave q2 => q_ret q2 = q_ret q
         | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
         | InfFuel => True
         end).

(* ==========================================================================
   7.  The dyn fast leg (as the v2 annex, plus the population bounds).
   ========================================================================== *)

Definition ZrLenDynLeg_STMT : Prop :=
  forall c q (ll dl : list nat) (entl entd : nat -> Code),
    ValidLengths ll 15%nat ->
    ValidLengths dl 15%nat ->
    zr_two_own_v3 (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) ll entl ->
    zr_two_own_v3 (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
        (t_distbits (s_tab (q_st q))) dl entd ->
    0 < t_lenbits (s_tab (q_st q)) <= 15 ->
    0 < t_distbits (s_tab (q_st q)) <= 15 ->
    zr_len_ents ll entl ->
    zr_dist_ents dl entd ->
    (length ll <= 286)%nat ->
    (length dl <= 30)%nat ->
    GtDecHsel.lcode_root_opshape
        (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) ->
    br_wf (q_br q) ->
    0 <= o_put (q_ob q) ->
    0 <= o_left (q_ob q) ->
    q_out q = o_put (q_ob q) + o_left (q_ob q) ->
    q_out q <= 4294967295 ->
    w_whave (s_win (q_st q)) = 0 ->
    t_sane (s_tab (q_st q)) <> 0 ->
    h_mode (s_hdr (q_st q)) = M_LEN ->
    (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q))) = true ->
    W2Stream.br_haligned (q_br q) ->
    br_have (q_br q) <= 4294967290 ->
    (exists k q' p rem,
       inf_iter k c q = Some q'
       /\ zr_syms_prefix ll dl (br_stream (q_br q)) p rem
       /\ p <> []
       /\ br_stream (q_br q') = rem
       /\ (length rem < length (br_stream (q_br q)))%nat
       /\ resolve_lz p (ob_slice (q_ob q) 0 (o_put (q_ob q)))
          = Some (ob_slice (q_ob q') 0 (o_put (q_ob q')))
       /\ h_mode (s_hdr (q_st q')) = M_LEN
       /\ br_wf (q_br q')
       /\ 0 <= o_put (q_ob q')
       /\ 0 <= o_left (q_ob q')
       /\ o_put (q_ob q') + o_left (q_ob q')
          = o_put (q_ob q) + o_left (q_ob q)
       /\ s_tab (q_st q') = s_tab (q_st q)
       /\ s_win (q_st q') = s_win (q_st q)
       /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
       /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
       /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
       (* amendment #11: h_check/h_total frame conjuncts — carrier
          q7-decode; g1 census; q6 pre-ruling;
          #10 shape *)
       /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
       /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
       /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
       /\ W2Stream.br_haligned (q_br q'))
    \/ (exists k q' p rem,
       inf_iter k c q = Some q'
       /\ zr_syms_prefix ll dl (br_stream (q_br q)) p rem
       /\ decode_lit_len ll dl rem = Some (LzEnd, br_stream (q_br q'))
       /\ resolve_lz p (ob_slice (q_ob q) 0 (o_put (q_ob q)))
          = Some (ob_slice (q_ob q') 0 (o_put (q_ob q')))
       /\ h_mode (s_hdr (q_st q')) = M_TYPE
       /\ br_wf (q_br q')
       /\ 0 <= o_put (q_ob q')
       /\ 0 <= o_left (q_ob q')
       /\ o_put (q_ob q') + o_left (q_ob q')
          = o_put (q_ob q) + o_left (q_ob q)
       /\ s_tab (q_st q') = s_tab (q_st q)
       /\ s_win (q_st q') = s_win (q_st q)
       /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
       /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
       /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
       (* amendment #11: h_check/h_total frame conjuncts — carrier
          q7-decode; g1 census; q6 pre-ruling;
          #10 shape *)
       /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
       /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
       /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
       /\ W2Stream.br_haligned (q_br q'))
    \/ (exists k q',
        inf_iter k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
    \/ (exists n s,
        inf_loop n c q = Some s
        /\ match s with
           | InfLeave q2 => q_ret q2 = q_ret q
           | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
           | InfFuel => True
           end).
