(** * Gap7FixSel — the FIXED-leg selection targets, statements only
    (g1 spells per the fastsel protocol; q7 proves against their
    W-corpus + the landed Q6Q walk, delta-convertible for g1's exact
    consumption in the ZrHuffFixedLegSel assembly).

    OWNER of the spellings: an earlier development run.  PROVER: q7-decode (their
    ownership ruling, this hour).

    SHAPE: the q6-vocabulary chain (ZReproQ6Q) at the CONCRETE fixed
    tables.  The generic loose-pack strengthened statement is FALSE
    (q7's fastsel countermodel, INBOX-1649); at the concrete tables the
    invalid-ent corners (symbols 286/287: coded 8-bit, no length_base
    entry) are DECIDED, and both sides fail together there — that
    no-bite analysis is the design premise, verified by the prover in
    the walk rather than assumed.

    DECLARED DELTAS vs the landed texts, and nothing else:
      (i)   [ll]/[dl] instantiated at [fixed_lit_lengths]/
            [fixed_dist_lengths] (quantifiers removed);
      (ii)  the four table-pin equations inserted, spelled exactly as
            ZrHuffFixedLeg's band (Q6HuffResidue :170-173);
      (iii) the mode-only M_BAD arm strengthened to carry the
            ENTRY-REBASED declarative failure (Gap7LoopSel's BAD-arm
            move, at the fixed lists);
      (iv)  in the loop statement, the fast-leg premise
            [ZrLenFastLeg] becomes [ZrLenFastLegFixSel_STMT].
    Sources: ZrLenFastLeg = ZReproQ6Q.v :178-275 verbatim;
    zr_sym_loop's statement = ZReproQ6Q.v :281-344 verbatim
    (amendment #10/#11 conjuncts included on every continuing arm).

    PA-EXPORTS: none (statements only).
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A ZReproL0E.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6M ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The strengthened-BAD failure payload at the fixed lists, at the
    ENTRY output slice (one abbreviation so both statements carry the
    identical text). *)
Definition zr_fix_dec_failure (q : InfSt) : Prop :=
  decode_symbols fixed_lit_lengths fixed_dist_lengths
    (br_stream (q_br q)) = None
  \/ (exists syms rem,
        decode_symbols fixed_lit_lengths fixed_dist_lengths
          (br_stream (q_br q)) = Some (syms, rem)
        /\ resolve_lz syms (ob_slice (q_ob q) 0 (o_put (q_ob q)))
           = None).

(** The fast leg at the fixed tables, selection form. *)
Definition ZrLenFastLegFixSel_STMT : Prop :=
  forall c q (entl entd : nat -> Code),
    t_lencode (s_tab (q_st q)) = TRlenfix ->
    t_lenbits (s_tab (q_st q)) = 9 ->
    t_distcode (s_tab (q_st q)) = TRdistfix ->
    t_distbits (s_tab (q_st q)) = 5 ->
    ValidLengths fixed_lit_lengths 15%nat ->
    ValidLengths fixed_dist_lengths 15%nat ->
    ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) fixed_lit_lengths 15%nat entl ->
    ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
        (t_distbits (s_tab (q_st q))) fixed_dist_lengths 15%nat entd ->
    0 < t_lenbits (s_tab (q_st q)) <= 15 ->
    0 < t_distbits (s_tab (q_st q)) <= 15 ->
    (forall sym cw, code_for fixed_lit_lengths 15%nat sym = Some cw ->
         sub_len (entl sym) = false) ->
    (forall sym cw, code_for fixed_dist_lengths 15%nat sym = Some cw ->
         sub_dist (entd sym) = false) ->
    zr_len_ents fixed_lit_lengths entl ->
    zr_dist_ents fixed_dist_lengths entd ->
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
    (* CONT: a nonempty prefix consumed, back at M_LEN *)
    (exists k q' p rem,
       inf_iter k c q = Some q'
       /\ zr_syms_prefix fixed_lit_lengths fixed_dist_lengths
            (br_stream (q_br q)) p rem
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
       /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
       /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
       /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
       /\ W2Stream.br_haligned (q_br q'))
    (* ENDED: a prefix plus the end-of-block, block done at M_TYPE *)
    \/ (exists k q' p rem,
       inf_iter k c q = Some q'
       /\ zr_syms_prefix fixed_lit_lengths fixed_dist_lengths
            (br_stream (q_br q)) p rem
       /\ decode_lit_len fixed_lit_lengths fixed_dist_lengths rem
          = Some (LzEnd, br_stream (q_br q'))
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
       /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
       /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
       /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
       /\ W2Stream.br_haligned (q_br q'))
    \/ (exists k q',
        inf_iter k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD
        /\ zr_fix_dec_failure q)
    \/ (exists n s,
        inf_loop n c q = Some s
        /\ match s with
           | InfLeave q2 => q_ret q2 = q_ret q
           | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
           | InfFuel => True
           end).

(** The symbol loop at the fixed tables, selection form. *)
Definition ZrSymLoopFixSel_STMT : Prop :=
  forall n c q (entl entd : nat -> Code),
  ZrLenFastLegFixSel_STMT ->
  t_lencode (s_tab (q_st q)) = TRlenfix ->
  t_lenbits (s_tab (q_st q)) = 9 ->
  t_distcode (s_tab (q_st q)) = TRdistfix ->
  t_distbits (s_tab (q_st q)) = 5 ->
  ValidLengths fixed_lit_lengths 15%nat ->
  ValidLengths fixed_dist_lengths 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) fixed_lit_lengths 15%nat entl ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) fixed_dist_lengths 15%nat entd ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for fixed_lit_lengths 15%nat sym = Some cw ->
       sub_len (entl sym) = false) ->
  (forall sym cw, code_for fixed_dist_lengths 15%nat sym = Some cw ->
       sub_dist (entd sym) = false) ->
  zr_len_ents fixed_lit_lengths entl ->
  zr_dist_ents fixed_dist_lengths entd ->
  GtDecHsel.lcode_root_opshape
      (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ->
  (length (br_stream (q_br q)) < n)%nat ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  h_mode (s_hdr (q_st q)) = M_LEN ->
  W2Stream.br_haligned (q_br q) ->
  br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
  (exists k q' syms rem,
     inf_iter k c q = Some q'
     /\ decode_symbols fixed_lit_lengths fixed_dist_lengths
          (br_stream (q_br q)) = Some (syms, rem)
     /\ br_stream (q_br q') = rem
     /\ resolve_lz syms (ob_slice (q_ob q) 0 (o_put (q_ob q)))
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
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ W2Stream.br_haligned (q_br q'))
  \/ (exists k q',
      inf_iter k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD
      /\ zr_fix_dec_failure q)
  \/ (exists n' s,
      inf_loop n' c q = Some s
      /\ match s with
         | InfLeave q2 => q_ret q2 = q_ret q
         | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
         | InfFuel => True
         end).
