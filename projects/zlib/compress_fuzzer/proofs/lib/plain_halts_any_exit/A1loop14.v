(** * A1loop14 — the 1.4 twin of A1loop.
    The symbol loop over RT's 1.4 flavour, consuming the FROZEN A1StmtsV3_14 leg (ZrLenDynLeg14_STMT) and trip
    (A1trip14.zr_sym_trip_dyn14).  Text twin of A1loop.v by tools/gen_twin14.py; by hand: the imports, and the gate
    destruct, which now carries the third conjunct (bits < 8) so that HG passes VERBATIM to both frozen premises
    (lens 3).  The iterate / loop composition is rt14-r2 (Inflate14Iter). *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate Inflate14 Inflate14Iter.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3 A1core A1trip A1StmtsV3_14 A1trip14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The trip twin, re-shaped as a plain forall for the loop's call
    (the _STMT constant unfolds at application). *)
Lemma zr_sym_loop_dyn14 :
  forall n c q (ll dl : list nat) (entl entd : nat -> Code),
  ZrLenDynLeg14_STMT ->
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
    intros c q ll dl entl entd HFast HVl HVd Hownl Hownd Hrbl Hrbd
           Hentsl Hentsd Hpopl Hpopd Hshl Hn Hwf Hput Hleft Htie Hcap Hwh Hsn Hm
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
                Hentsl Hentsd Hpopl Hpopd Hshl Hwf Hput Hleft Htie Hcap
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
    destruct (zr_sym_trip_dyn14 c q ll dl entl entd HVl HVd Hownl Hownd Hrbl
                Hrbd Hentsl Hentsd Hpopl Hpopd Hwf Hput Hleft Htie Hcap
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

