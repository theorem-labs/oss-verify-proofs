(** * LkLoopDyn — THE DYN SYMBOL LOOP, GOOD-ONLY (q7-decode leavekill
    fork, 2026-08-22, OFF-TREE SCRATCH).

    LkLoopGood's induction at the TIGHT two-level packs (mirroring
    g1's Gap7LoopSel.zr_sym_loop_dyn_sel): iteration lemmas are the
    good-only [lk_fast_leg_dyn_good] / [lk_sym_trip_dyn_good]; the
    whave-0 totality context [lk_ctx_wf0] rides the walk through
    [lk_ctx0_transport].  BAD arms are refuted by determinism against
    the block's declarative success; no leave/fuel arm exists below.

    PA-EXPORT: lk_sym_loop_dyn_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3 W5Bridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Ents.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  LkBody LkTripDyn LkFastDyn LkLoopGood.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma lk_sym_loop_dyn_good :
  forall n c q (ll dl : list nat) (entl entd : nat -> Code)
         (syms : list lz_sym) (r3 : list bool) (out : list Z),
  ValidLengths ll 15%nat ->
  ValidLengths dl 15%nat ->
  zr_two_own_v3 (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll entl ->
  zr_two_own_v3 (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl entd ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  zr_len_ents3 ll entl ->
  zr_dist_ents1 dl entd ->
  (length ll <= 286)%nat ->
  (length dl <= 30)%nat ->
  GtDecHsel.lcode_root_opshape
      (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ->
  lk_ctx_wf0 (if_ctx (w5_args q)) ->
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
  decode_symbols ll dl (br_stream (q_br q)) = Some (syms, r3) ->
  resolve_lz syms (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some out ->
  zlen out <= q_out q ->
  exists k q',
     inf_iter k c q = Some q'
     /\ br_stream (q_br q') = r3
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
     /\ W2Stream.br_haligned (q_br q').
Proof.
  intro n.
  induction n as [|n IHn];
    intros c q ll dl entl entd syms r3 out HVl HVd Hownl Hownd Hrbl
           Hrbd Hentsl Hentsd Hpopl Hpopd Hshl Hctx0 Hn Hwf
           Hput Hleft Htie Hcap Hwh Hsn Hm Hha Hbud HD HR HRoom;
    [lia|].
  pose proof (zr_slice_length (q_ob q) (o_put (q_ob q))) as HslL.
  (* the shared continuation: from a post-step M_LEN state q3 *)
  assert (RECUR : forall q3 (tail : list lz_sym),
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
      decode_symbols ll dl (br_stream (q_br q3)) = Some (tail, r3) ->
      resolve_lz tail (ob_slice (q_ob q3) 0 (o_put (q_ob q3))) = Some out ->
      exists k q',
        inf_iter k c q3 = Some q'
        /\ br_stream (q_br q') = r3
        /\ resolve_lz tail (ob_slice (q_ob q3) 0 (o_put (q_ob q3)))
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
        /\ W2Stream.br_haligned (q_br q')).
  { intros q3 tail Htab3 Hwin3 Hout3 Hlen3 Hwf3 Hput3 Hleft3 Hsum3 Hm3
           Hha3 Hbud3 HD3 HR3.
    apply (IHn c q3 ll dl entl entd tail r3 out); try assumption.
    - rewrite Htab3, (tbl_of_stable (q_st q) (q_st q3) _ Htab3).
      exact Hownl.
    - rewrite Htab3, (tbl_of_stable (q_st q) (q_st q3) _ Htab3).
      exact Hownd.
    - rewrite Htab3. exact Hrbl.
    - rewrite Htab3. exact Hrbd.
    - rewrite Htab3, (tbl_of_stable (q_st q) (q_st q3) _ Htab3).
      exact Hshl.
    - exact (lk_ctx0_transport q q3 Htab3 Hwin3 Hctx0).
    - rewrite Hout3, Hsum3. exact Htie.
    - rewrite Hout3. exact Hcap.
    - rewrite Hwin3. exact Hwh.
    - rewrite Htab3. exact Hsn.
    - rewrite Hout3. exact HRoom. }
  destruct (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)))
    eqn:HG.
  - (* fast entry *)
    assert (Hcap5 : br_have (q_br q) <= 4294967290).
    { destruct Hwf as (Hb & _).
      pose proof (Z.div_pos (br_bits (q_br q)) 8 ltac:(lia) ltac:(lia)).
      lia. }
    destruct (lk_fast_leg_dyn_good c q ll dl entl entd HVl HVd Hownl
                Hownd Hrbl Hrbd Hentsl Hentsd Hpopl Hpopd Hshl Hctx0
                Hwf Hput Hleft Htie Hcap Hwh Hsn Hm HG Hha Hcap5)
      as [ (k1 & q3 & p & rem & HI & Hpre & Hne & Hstr & Hshort & Hres
            & Hm3 & Hwf3 & Hput3 & Hleft3 & Hsum3 & Htab3 & Hwin3
            & Hlast3 & Hwrap3 & Hfl3 & Hck3 & Hto3 & Hret3 & Hin3
            & Hout3 & Hha3)
         | [ (k1 & q3 & p & rem & HI & Hpre & Hend & Hres & Hm3 & Hwf3
              & Hput3 & Hleft3 & Hsum3 & Htab3 & Hwin3 & Hlast3 & Hwrap3
              & Hfl3 & Hck3 & Hto3 & Hret3 & Hin3 & Hout3 & Hha3)
           | (k1 & q3 & HI & HM3 & HFail) ] ].
    + (* fast CONT: peel the prefix and recurse *)
      destruct (lk_prefix_peel ll dl p (br_stream (q_br q)) rem syms r3
                  Hpre HD)
        as (tail & HDrem & Esyms).
      assert (HD3 : decode_symbols ll dl (br_stream (q_br q3))
                    = Some (tail, r3))
        by (rewrite Hstr; exact HDrem).
      assert (HRsplit : exists mid,
          resolve_lz p (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some mid
          /\ resolve_lz tail mid = Some out).
      { apply lk_resolve_split.
        - exact (zr_syms_prefix_no_end ll dl p _ _ Hpre).
        - rewrite <- Esyms. exact HR. }
      destruct HRsplit as (mid & HRp & HRtail).
      assert (Emid : mid = ob_slice (q_ob q3) 0 (o_put (q_ob q3)))
        by (rewrite HRp in Hres; injection Hres as E; exact E).
      subst mid.
      assert (Hbud3 : br_have (q_br q3) + br_bits (q_br q3) / 8
                      <= 4294967290).
      { pose proof (br_budget_mono (q_br q) (q_br q3) Hwf Hwf3
                      ltac:(rewrite Hstr; lia)) as HBM. lia. }
      destruct (RECUR q3 tail Htab3 Hwin3 Hout3
                  ltac:(rewrite Hstr; lia) Hwf3 Hput3 Hleft3 Hsum3 Hm3
                  Hha3 Hbud3 HD3 HRtail)
        as (k2 & q' & HI2 & HS2 & HR2 & HM2 & C6 & C7 & C8 & C9 & C10
            & C11 & C12 & C13 & CF & CK & CT & C14 & C15 & C16 & CH).
      exists (k1 + k2)%nat, q'.
      split. { rewrite (inf_iter_add k1 k2 c q q3 HI). exact HI2. }
      split. { exact HS2. }
      split.
      { rewrite Esyms.
        rewrite (zr_resolve_app p tail _ _
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
    + (* fast ENDED: the block closes here *)
      assert (HDend : decode_symbols ll dl (br_stream (q_br q))
                      = Some (p ++ [LzEnd], br_stream (q_br q3))).
      { apply (zr_syms_prefix_decode ll dl p _ rem _ _ Hpre).
        rewrite decode_symbols_unfold, Hend. reflexivity. }
      rewrite HD in HDend. injection HDend as Es Er.
      exists k1, q3.
      split. { exact HI. }
      split. { exact (eq_sym Er). }
      split.
      { rewrite Es.
        rewrite (zr_resolve_app p [LzEnd] _ _
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
    + (* fast BAD: refuted by the premise *)
      exfalso.
      destruct HFail as [HdN | (syms' & rem' & HdS & HrN)].
      * rewrite HD in HdN. discriminate.
      * rewrite HD in HdS. injection HdS as Es _. subst syms'.
        rewrite HR in HrN. discriminate.
  - (* slow entry: one symbol *)
    rewrite decode_symbols_unfold in HD.
    destruct (decode_lit_len ll dl (br_stream (q_br q)))
      as [[sy rem]|] eqn:Hd1; [|discriminate HD].
    cbv beta iota in HD.
    destruct (lz_is_end sy) eqn:Hisend.
    + (* the end symbol: the trip closes the block *)
      pose proof (lz_is_end_true sy Hisend) as Esy. subst sy.
      injection HD as Es Er. subst syms r3.
      destruct (lk_sym_trip_dyn_good c q ll dl entl entd LzEnd rem HVl
                  HVd Hownl Hownd Hrbl Hrbd Hentsl Hentsd Hpopl Hpopd
                  Hwf Hput Hleft Htie Hcap Hwh Hsn Hm HG Hd1 I)
        as (k1 & q3 & HI & Hdec3 & Hsy & Hwf3 & Hput3 & Hleft3 & Hsum3
            & Htab3 & Hwin3 & Hlast3 & Hwrap3 & Hret3 & Hin3 & Hout3
            & Hha3i & Hfl3 & Hck3 & Hto3).
      destruct Hsy as (Hob & Hm3).
      rewrite Hd1 in Hdec3. injection Hdec3 as Er3.
      exists k1, q3.
      split. { exact HI. }
      split. { symmetry. exact Er3. }
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
    + (* a body symbol, then recurse *)
      destruct (decode_symbols ll dl rem)
        as [[tail r3']|] eqn:HDtail; [|discriminate HD].
      injection HD as Es Er. subst syms r3'.
      assert (Hroom : match sy with
                      | LzLit _ => 0 < o_left (q_ob q)
                      | LzEnd => True
                      | LzRef len dist =>
                          Z.of_nat dist <= o_put (q_ob q)
                          /\ Z.of_nat len <= o_left (q_ob q)
                      end
              /\ resolve_lz tail
                   (ob_slice (q_ob q) 0 (o_put (q_ob q))
                    ++ match sy with
                       | LzLit v => [v]
                       | LzRef len dist =>
                           lz_copy (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                                   len dist
                       | LzEnd => []
                       end) = Some out).
      { pose proof HRoom as HRoomZ. unfold zlen in HRoomZ.
        destruct sy as [v|len dist|]; [| |discriminate Hisend].
        - cbn [resolve_lz] in HR.
          pose proof (lk_resolve_len_mono tail _ _ HR) as Hmono.
          rewrite length_app, HslL in Hmono. cbn [length] in Hmono.
          split; [lia | exact HR].
        - cbn [resolve_lz] in HR.
          destruct ((dist =? 0)%nat
                    || (length (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                        <? dist)%nat) eqn:G; [discriminate HR|].
          apply orb_false_iff in G. destruct G as (G0 & Glt).
          apply Nat.ltb_ge in Glt. rewrite HslL in Glt.
          pose proof (lk_resolve_len_mono tail _ _ HR) as Hmono.
          rewrite length_app, HslL, lz_copy_length in Hmono.
          split; [split; lia | exact HR]. }
      destruct Hroom as (Hroom & HRtail).
      destruct (lk_sym_trip_dyn_good c q ll dl entl entd sy rem HVl HVd
                  Hownl Hownd Hrbl Hrbd Hentsl Hentsd Hpopl Hpopd
                  Hwf Hput Hleft Htie Hcap Hwh Hsn Hm HG Hd1 Hroom)
        as (k1 & q3 & HI & Hdec3 & Hsy & Hwf3 & Hput3 & Hleft3 & Hsum3
            & Htab3 & Hwin3 & Hlast3 & Hwrap3 & Hret3 & Hin3 & Hout3
            & Hha3i & Hfl3 & Hck3 & Hto3).
      rewrite Hd1 in Hdec3. injection Hdec3 as Er3.
      assert (Hshort : (length (br_stream (q_br q3))
                        < length (br_stream (q_br q)))%nat).
      { rewrite <- Er3.
        exact (decode_lit_len_shorter ll dl _ _ _ Hd1). }
      assert (Hbud3 : br_have (q_br q3) + br_bits (q_br q3) / 8
                      <= 4294967290).
      { pose proof (br_budget_mono (q_br q) (q_br q3) Hwf Hwf3
                      ltac:(lia)) as HBM. lia. }
      assert (HD3 : decode_symbols ll dl (br_stream (q_br q3))
                    = Some (tail, r3))
        by (rewrite <- Er3; exact HDtail).
      assert (HR3 : resolve_lz tail
                      (ob_slice (q_ob q3) 0 (o_put (q_ob q3)))
                    = Some out).
      { destruct sy as [v|len dist|]; [| |discriminate Hisend].
        - destruct Hsy as (Hsl & _). rewrite Hsl. exact HRtail.
        - destruct Hsy as (_ & _ & Hsl & _). rewrite Hsl. exact HRtail. }
      assert (Hm3' : h_mode (s_hdr (q_st q3)) = M_LEN).
      { destruct sy as [v|len dist|]; [| |discriminate Hisend].
        - exact (proj2 Hsy).
        - destruct Hsy as (_ & _ & _ & HmM). exact HmM. }
      destruct (RECUR q3 tail Htab3 Hwin3 Hout3 ltac:(lia) Hwf3 Hput3
                  Hleft3 Hsum3 Hm3' (Hha3i Hha) Hbud3 HD3 HR3)
        as (k2 & q' & HI2 & HS2 & HR2 & HM2 & C6 & C7 & C8 & C9 & C10
            & C11 & C12 & C13 & CF & CK & CT & C14 & C15 & C16 & CH).
      exists (k1 + k2)%nat, q'.
      split. { rewrite (inf_iter_add k1 k2 c q q3 HI). exact HI2. }
      split. { exact HS2. }
      split.
      { destruct sy as [v|len dist|]; [| |discriminate Hisend].
        - cbn [resolve_lz].
          destruct Hsy as (Hsl & _).
          rewrite <- Hsl. exact HR2.
        - destruct Hsy as (Hne0 & Hdle & Hsl & _).
          cbn [resolve_lz].
          rewrite Hne0.
          rewrite (proj2 (Nat.ltb_ge
                     (length (ob_slice (q_ob q) 0 (o_put (q_ob q)))) dist)
                     ltac:(rewrite HslL; lia)).
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
Qed.

Set Printing Width 2000.
Print Assumptions lk_sym_loop_dyn_good.
