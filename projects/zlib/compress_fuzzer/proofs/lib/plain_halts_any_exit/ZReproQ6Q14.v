(* the zlib 1.4 twin of ZReproQ6Q, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from ZReproQ6Q), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * ZReproQ6Q — the symbol loop: [decode_symbols]/[resolve_lz]
    composition over the per-symbol trip (LEN-chain layer 3).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).

    [zr_syms_prefix] is the non-end prefix-consumption relation the FAST
    path's residue ([ZrLenFastLeg], the inflate_fast decode-agreement
    mountain's interface) and the slow trips both speak; the loop
    dispatches each [M_LEN] entry on the fast guard and composes either
    into the block-final [decode_symbols]/[resolve_lz] agreement.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
(* amendment window 2 (q7-decode per TL grant 2026-08-20; owner review
   trails): br_haligned + the input budget enter the fast-leg interface. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14 Spec.PngModel.Inflate14Iter ZReproQ6P14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Non-end prefix consumption, and its composition laws.
   ========================================================================== *)






(* ==========================================================================
   2.  THE FAST-PATH RESIDUE (statement-only): the inflate_fast
       decode-agreement mountain's interface.  When the fast guard holds
       at an [M_LEN] entry, [if_model]'s work IS the consumption of a
       NONEMPTY non-end symbol prefix (or ends the block at the EOB, or
       goes BAD, or is absorbed).  Discharge owner: TBD (the fast->slow
       reduction, or a direct walk over if_body).
   ========================================================================== *)

(* retained per fleet retention convention; superseded by amendment
   window 2 (gb-opshape spliced the pre-amendment staging; this window
   carries negotiation items 5 and 7 plus the pack pins in ZReproQ6P). *)

Definition ZrLenFastLeg14 : Prop :=
  forall c q (ll dl : list nat) (entl entd : nat -> Code),
    ValidLengths ll 15%nat ->
    ValidLengths dl 15%nat ->
    ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
        (t_lenbits (s_tab (q_st q))) ll 15%nat entl ->
    ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
        (t_distbits (s_tab (q_st q))) dl 15%nat entd ->
    0 < t_lenbits (s_tab (q_st q)) <= 15 ->
    0 < t_distbits (s_tab (q_st q)) <= 15 ->
    (forall sym cw, code_for ll 15%nat sym = Some cw ->
         sub_len (entl sym) = false) ->
    (forall sym cw, code_for dl 15%nat sym = Some cw ->
         sub_dist (entd sym) = false) ->
    zr_len_ents ll entl ->
    zr_dist_ents dl entd ->
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
    (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8) = true ->
    W2Stream.br_haligned (q_br q) ->
    br_have (q_br q) <= 4294967290 ->
    (* CONT: a nonempty prefix consumed, back at M_LEN *)
    (exists k q' p rem,
       inf_iter14 k c q = Some q'
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
       (* amendment #10 (q7-decode as TL-confirmed carrier, 2026-08-20;
          spec = AMENDMENT-10-FREEZE.md ): the flags clause on
          both continuing arms, and the ENDED arm's reader alignment —
          the walk's zr_body_exit needs both THROUGH the huffman
          residue, whose fixed-leg discharger (Q6S) exits via this
          Prop's arms.  W4Fold's ExType pack already exported the
          alignment; these conjuncts stop discarding it. *)
       /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
       (* amendment #11: h_check/h_total frame conjuncts — carrier
          q7-decode; g1 census; q6 pre-ruling;
          #10 shape *)
       /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
       /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
       /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
       /\ W2Stream.br_haligned (q_br q'))
    (* ENDED: a prefix plus the end-of-block, block done at M_TYPE *)
    \/ (exists k q' p rem,
       inf_iter14 k c q = Some q'
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
        inf_iter14 k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
    \/ (exists n s,
        inf_loop14 n c q = Some s
        /\ match s with
           | InfLeave q2 => q_ret q2 = q_ret q
           | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
           | InfFuel => True
           end).

(* ==========================================================================
   3.  THE SYMBOL LOOP.
   ========================================================================== *)

Lemma zr_sym_loop14 :
  forall n c q (ll dl : list nat) (entl entd : nat -> Code),
  ZrLenFastLeg14 ->
  ValidLengths ll 15%nat ->
  ValidLengths dl 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll 15%nat entl ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl 15%nat entd ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for ll 15%nat sym = Some cw ->
       sub_len (entl sym) = false) ->
  (forall sym cw, code_for dl 15%nat sym = Some cw ->
       sub_dist (entd sym) = false) ->
  zr_len_ents ll entl ->
  zr_dist_ents dl entd ->
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
     inf_iter14 k c q = Some q'
     /\ decode_symbols ll dl (br_stream (q_br q)) = Some (syms, rem)
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
     (* amendment #11: h_check/h_total frame conjuncts — carrier
        q7-decode; g1 census; q6 pre-ruling;
        #10 shape *)
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ W2Stream.br_haligned (q_br q'))
  \/ (exists k q',
      inf_iter14 k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists n' s,
      inf_loop14 n' c q = Some s
      /\ match s with
         | InfLeave q2 => q_ret q2 = q_ret q
         | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
         | InfFuel => True
         end).
Proof.
  induction n as [|n IHn];
    intros c q ll dl entl entd HFast HVl HVd Hownl Hownd Hrbl Hrbd Hsubl
           Hsubd Hentsl Hentsd Hshl Hn Hwf Hput Hleft Htie Hcap Hwh Hsn Hm
           Hha Hbud;
    [lia|].
  (* the shared continuation: from a post-trip M_LEN state q3 *)
  assert (RECUR : forall q3,
      s_tab (q_st q3) = s_tab (q_st q) ->
      s_win (q_st q3) = s_win (q_st q) ->
      q_out q3 = q_out q ->
      (length (br_stream (q_br q3)) < n)%nat ->
      br_wf (q_br q3) ->
      0 <= o_put (q_ob q3) ->
      0 <= o_left (q_ob q3) ->
      o_put (q_ob q3) + o_left (q_ob q3) = o_put (q_ob q) + o_left (q_ob q) ->
      h_mode (s_hdr (q_st q3)) = M_LEN ->
      W2Stream.br_haligned (q_br q3) ->
      br_have (q_br q3) + br_bits (q_br q3) / 8 <= 4294967290 ->
      (exists k q' syms rem,
         inf_iter14 k c q3 = Some q'
         /\ decode_symbols ll dl (br_stream (q_br q3)) = Some (syms, rem)
         /\ br_stream (q_br q') = rem
         /\ resolve_lz syms (ob_slice (q_ob q3) 0 (o_put (q_ob q3)))
            = Some (ob_slice (q_ob q') 0 (o_put (q_ob q')))
         /\ h_mode (s_hdr (q_st q')) = M_TYPE
         /\ br_wf (q_br q')
         /\ 0 <= o_put (q_ob q')
         /\ 0 <= o_left (q_ob q')
         /\ o_put (q_ob q') + o_left (q_ob q')
            = o_put (q_ob q3) + o_left (q_ob q3)
         /\ s_tab (q_st q') = s_tab (q_st q3)
         /\ s_win (q_st q') = s_win (q_st q3)
         /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q3))
         /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q3))
         /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q3))
         /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q3))
         /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q3))
         /\ q_ret q' = q_ret q3 /\ q_in q' = q_in q3 /\ q_out q' = q_out q3
         /\ W2Stream.br_haligned (q_br q'))
      \/ (exists k q',
          inf_iter14 k c q3 = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
      \/ (exists n' s,
          inf_loop14 n' c q3 = Some s
          /\ match s with
             | InfLeave q2 => q_ret q2 = q_ret q3
             | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
             | InfFuel => True
             end)).
  { intros q3 Htab3 Hwin3 Hout3 Hlen3 Hwf3 Hput3 Hleft3 Hsum3 Hm3 Hha3
           Hbud3.
    apply (IHn c q3 ll dl entl entd HFast HVl HVd); try assumption.
    - rewrite Htab3, (tbl_of_stable (q_st q) (q_st q3) _ Htab3).
      exact Hownl.
    - rewrite Htab3, (tbl_of_stable (q_st q) (q_st q3) _ Htab3).
      exact Hownd.
    - rewrite Htab3. exact Hrbl.
    - rewrite Htab3. exact Hrbd.
    - rewrite Htab3, (tbl_of_stable (q_st q) (q_st q3) _ Htab3).
      exact Hshl.
    - rewrite Hout3, Hsum3. exact Htie.
    - rewrite Hout3. exact Hcap.
    - rewrite Hwin3. exact Hwh.
    - rewrite Htab3. exact Hsn. }
  destruct (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8)
    eqn:HG.
  - (* fast entry: the named residue *)
    assert (Hcap5 : br_have (q_br q) <= 4294967290).
    { destruct Hwf as (Hb & _).
      pose proof (Z.div_pos (br_bits (q_br q)) 8 ltac:(lia) ltac:(lia)).
      lia. }
    destruct (HFast c q ll dl entl entd HVl HVd Hownl Hownd Hrbl Hrbd
                Hsubl Hsubd Hentsl Hentsd Hshl Hwf Hput Hleft Htie Hcap
                Hwh Hsn Hm HG Hha Hcap5)
      as [ (k1 & q3 & p & rem & HI & Hpre & Hne & Hstr & Hshort & Hres
            & Hm3 & Hwf3 & Hput3 & Hleft3 & Hsum3 & Htab3 & Hwin3
            & Hlast3 & Hwrap3 & Hfl3 & Hck3 & Hto3 & Hret3 & Hin3
            & Hout3 & Hha3)
         | [ (k1 & q3 & p & rem & HI & Hpre & Hend & Hres & Hm3 & Hwf3
              & Hput3 & Hleft3 & Hsum3 & Htab3 & Hwin3 & Hlast3 & Hwrap3
              & Hfl3 & Hck3 & Hto3 & Hret3 & Hin3 & Hout3 & Hha3)
           | [ BAD | EX ] ] ].
    + (* fast CONT: recurse after the prefix *)
      assert (Hbud3 : br_have (q_br q3) + br_bits (q_br q3) / 8
                      <= 4294967290).
      { pose proof (br_budget_mono (q_br q) (q_br q3) Hwf Hwf3
                      ltac:(rewrite Hstr; lia)) as HBM. lia. }
      destruct (RECUR q3 Htab3 Hwin3 Hout3
                  ltac:(rewrite Hstr; lia) Hwf3 Hput3 Hleft3 Hsum3 Hm3
                  Hha3 Hbud3)
        as [ (k2 & q' & syms & rem' & HI2 & HD2 & HS2 & HR2 & HM2 & C6
              & C7 & C8 & C9 & C10 & C11 & C12 & C13 & CF & CK & CT & C14 & C15 & C16 & CH)
           | [ (k2 & q' & HI2 & HM2) | (n2 & sx & HL2 & HX2) ] ].
      * left. exists (k1 + k2)%nat, q', (p ++ syms), rem'.
        split. { rewrite (inf_iter14_add k1 k2 c q q3 HI). exact HI2. }
        split.
        { apply (zr_syms_prefix_decode ll dl p _ rem _ rem' Hpre).
          rewrite <- Hstr. exact HD2. }
        split. { exact HS2. }
        split.
        { rewrite (zr_resolve_app p syms _ _
                     (zr_syms_prefix_no_end ll dl p _ _ Hpre) Hres).
          exact HR2. }
        split. { exact HM2. }
        split. { exact C6. }
        split. { exact C7. }
        split. { exact C8. }
        split. { rewrite C9. exact Hsum3. }
        split. { rewrite C10. exact Htab3. }
        split. { rewrite C11. exact Hwin3. }
        split. { rewrite C12. exact Hlast3. }
        split. { rewrite C13. exact Hwrap3. }
        split. { rewrite CF. exact Hfl3. }
        split. { rewrite CK. exact Hck3. }
        split. { rewrite CT. exact Hto3. }
        split. { rewrite C14. exact Hret3. }
        split. { rewrite C15. exact Hin3. }
        split. { rewrite C16. exact Hout3. }
        exact CH.
      * right; left. exists (k1 + k2)%nat, q'.
        split; [ rewrite (inf_iter14_add k1 k2 c q q3 HI); exact HI2
               | exact HM2 ].
      * right; right. exists (k1 + n2)%nat, sx.
        split; [ exact (inf_loop14_after_iter k1 c q q3 n2 sx HI HL2) |].
        destruct sx as [qx|qx|qx r| |]; try exact HX2.
        rewrite HX2. exact Hret3.
    + (* fast ENDED: the block closes here *)
      left. exists k1, q3, (p ++ [LzEnd]), (br_stream (q_br q3)).
      split. { exact HI. }
      split.
      { apply (zr_syms_prefix_decode ll dl p _ rem _ _ Hpre).
        rewrite decode_symbols_unfold, Hend. reflexivity. }
      split. { reflexivity. }
      split.
      { rewrite (zr_resolve_app p [LzEnd] _ _
                   (zr_syms_prefix_no_end ll dl p _ _ Hpre) Hres).
        reflexivity. }
      split. { exact Hm3. }
      split. { exact Hwf3. }
      split. { exact Hput3. }
      split. { exact Hleft3. }
      split. { exact Hsum3. }
      split. { exact Htab3. }
      split. { exact Hwin3. }
      split. { exact Hlast3. }
      split. { exact Hwrap3. }
      split. { exact Hfl3. }
      split. { exact Hck3. }
      split. { exact Hto3. }
      split. { exact Hret3. }
      split. { exact Hin3. }
      split. { exact Hout3. }
      exact Hha3.
    + right; left. exact BAD.
    + right; right. exact EX.
  - (* slow entry: one symbol trip *)
    destruct (zr_sym_trip14 c q ll dl entl entd HVl HVd Hownl Hownd Hrbl
                Hrbd Hsubl Hsubd Hentsl Hentsd Hwf Hput Hleft Htie Hcap
                Hwh Hsn Hm HG)
      as [ (k1 & q3 & sy & HI & Hdec & Hsy & Hwf3 & Hput3 & Hleft3
            & Hsum3 & Htab3 & Hwin3 & Hlast3 & Hwrap3 & Hret3 & Hin3
            & Hout3 & Hha3i & Hfl3 & Hck3 & Hto3)
         | [ BAD | EX ] ];
      [ | right; left; exact BAD | right; right; exact EX ].
    assert (Hshort : (length (br_stream (q_br q3))
                      < length (br_stream (q_br q)))%nat).
    { exact (decode_lit_len_shorter ll dl _ _ _ Hdec). }
    assert (Hbud3 : br_have (q_br q3) + br_bits (q_br q3) / 8
                    <= 4294967290).
    { pose proof (br_budget_mono (q_br q) (q_br q3) Hwf Hwf3
                    ltac:(lia)) as HBM. lia. }
    destruct sy as [v|len dist|].
    + (* literal: recurse *)
      destruct Hsy as (Hsl & Hm3).
      destruct (RECUR q3 Htab3 Hwin3 Hout3 ltac:(lia) Hwf3 Hput3 Hleft3
                  Hsum3 Hm3 (Hha3i Hha) Hbud3)
        as [ (k2 & q' & syms & rem' & HI2 & HD2 & HS2 & HR2 & HM2 & C6
              & C7 & C8 & C9 & C10 & C11 & C12 & C13 & CF & CK & CT & C14 & C15 & C16 & CH)
           | [ (k2 & q' & HI2 & HM2) | (n2 & sx & HL2 & HX2) ] ].
      * left. exists (k1 + k2)%nat, q', (LzLit v :: syms), rem'.
        split. { rewrite (inf_iter14_add k1 k2 c q q3 HI). exact HI2. }
        split.
        { rewrite decode_symbols_unfold, Hdec. cbv beta iota.
          rewrite HD2. reflexivity. }
        split. { exact HS2. }
        split.
        { cbn [resolve_lz]. rewrite <- Hsl. exact HR2. }
        split. { exact HM2. }
        split. { exact C6. }
        split. { exact C7. }
        split. { exact C8. }
        split. { rewrite C9. exact Hsum3. }
        split. { rewrite C10. exact Htab3. }
        split. { rewrite C11. exact Hwin3. }
        split. { rewrite C12. exact Hlast3. }
        split. { rewrite C13. exact Hwrap3. }
        split. { rewrite CF. exact Hfl3. }
        split. { rewrite CK. exact Hck3. }
        split. { rewrite CT. exact Hto3. }
        split. { rewrite C14. exact Hret3. }
        split. { rewrite C15. exact Hin3. }
        split. { rewrite C16. exact Hout3. }
        exact CH.
      * right; left. exists (k1 + k2)%nat, q'.
        split; [ rewrite (inf_iter14_add k1 k2 c q q3 HI); exact HI2
               | exact HM2 ].
      * right; right. exists (k1 + n2)%nat, sx.
        split; [ exact (inf_loop14_after_iter k1 c q q3 n2 sx HI HL2) |].
        destruct sx as [qx|qx|qx r| |]; try exact HX2.
        rewrite HX2. exact Hret3.
    + (* reference: recurse *)
      destruct Hsy as (Hne0 & Hle & Hsl & Hm3).
      destruct (RECUR q3 Htab3 Hwin3 Hout3 ltac:(lia) Hwf3 Hput3 Hleft3
                  Hsum3 Hm3 (Hha3i Hha) Hbud3)
        as [ (k2 & q' & syms & rem' & HI2 & HD2 & HS2 & HR2 & HM2 & C6
              & C7 & C8 & C9 & C10 & C11 & C12 & C13 & CF & CK & CT & C14 & C15 & C16 & CH)
           | [ (k2 & q' & HI2 & HM2) | (n2 & sx & HL2 & HX2) ] ].
      * left. exists (k1 + k2)%nat, q', (LzRef len dist :: syms), rem'.
        split. { rewrite (inf_iter14_add k1 k2 c q q3 HI). exact HI2. }
        split.
        { rewrite decode_symbols_unfold, Hdec. cbv beta iota.
          rewrite HD2. reflexivity. }
        split. { exact HS2. }
        split.
        { cbn [resolve_lz].
          rewrite Hne0.
          rewrite (proj2 (Nat.ltb_ge
                     (length (ob_slice (q_ob q) 0 (o_put (q_ob q)))) dist)
                     ltac:(rewrite zr_slice_length; lia)).
          cbn [orb]. rewrite <- Hsl. exact HR2. }
        split. { exact HM2. }
        split. { exact C6. }
        split. { exact C7. }
        split. { exact C8. }
        split. { rewrite C9. exact Hsum3. }
        split. { rewrite C10. exact Htab3. }
        split. { rewrite C11. exact Hwin3. }
        split. { rewrite C12. exact Hlast3. }
        split. { rewrite C13. exact Hwrap3. }
        split. { rewrite CF. exact Hfl3. }
        split. { rewrite CK. exact Hck3. }
        split. { rewrite CT. exact Hto3. }
        split. { rewrite C14. exact Hret3. }
        split. { rewrite C15. exact Hin3. }
        split. { rewrite C16. exact Hout3. }
        exact CH.
      * right; left. exists (k1 + k2)%nat, q'.
        split; [ rewrite (inf_iter14_add k1 k2 c q q3 HI); exact HI2
               | exact HM2 ].
      * right; right. exists (k1 + n2)%nat, sx.
        split; [ exact (inf_loop14_after_iter k1 c q q3 n2 sx HI HL2) |].
        destruct sx as [qx|qx|qx r| |]; try exact HX2.
        rewrite HX2. exact Hret3.
    + (* end of block: done *)
      destruct Hsy as (Hob & Hm3).
      left. exists k1, q3, [LzEnd], (br_stream (q_br q3)).
      split. { exact HI. }
      split.
      { rewrite decode_symbols_unfold, Hdec. reflexivity. }
      split. { reflexivity. }
      split.
      { cbn [resolve_lz]. rewrite Hob. reflexivity. }
      split. { exact Hm3. }
      split. { exact Hwf3. }
      split. { exact Hput3. }
      split. { exact Hleft3. }
      split. { exact Hsum3. }
      split. { exact Htab3. }
      split. { exact Hwin3. }
      split. { exact Hlast3. }
      split. { exact Hwrap3. }
      split. { exact Hfl3. }
      split. { exact Hck3. }
      split. { exact Hto3. }
      split. { exact Hret3. }
      split. { exact Hin3. }
      split. { exact Hout3. }
      exact (Hha3i Hha).
Qed.


