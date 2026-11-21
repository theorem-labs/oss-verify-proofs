(** * BsAsm — ladder (b)+(c): the block walk in selection form, and the
    frozen heads (an earlier development run bodyasm fork).

    bs_blocks mirrors ZReproQ6W.zr_body_blocks GOOD-ONLY: the TYPEDO
    starve dies by BsSupport.bs_typedo_cont (K1); the dispatch BAD dies
    by zr_typedo_sound_plus's refutable arm against dec_blk_strict's
    success (weakened); the stored arm is BsStored's good-only trip;
    the fixed/dyn arms are the leavekill K2/K3 good-only legs (the dyn
    EOB carrier from BsSupport.bs_dec_256); room threads by
    BsSupport.bs_zlen_mono.  bs_close mirrors zr_body_tail good-only.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff InflateFast Inflate DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6B ZReproQ6I ZReproQ6Q ZReproQ6W ZReproL0E W2Stream GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill LkK2 LkK3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Sib Gap7BodySel GtBodySelect.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import BsSupport BsStored.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Definition bs_pack (c : InfCtx) (q : InfSt) (X : list Z) (rem : list bool)
  : Prop :=
  exists k q',
    inf_iter k c q = Some q'
    /\ br_stream (q_br q') = rem
    /\ ob_slice (q_ob q') 0 (o_put (q_ob q')) = X
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
    /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
    /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
    /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
    /\ W2Stream.br_haligned (q_br q')
    /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290
    /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
    /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)).

(** The close: final block exits, non-final recurses (zr_body_tail's
    good-only mirror at the strict fuel). *)
Lemma bs_close : forall (n' f : nat) c q (k13 : nat) q3 X rem,
  (forall q0 (fs0 : nat) X0 rem0,
      (length (br_stream (q_br q0)) < n')%nat ->
      zr_body_entry q0 ->
      h_mode (s_hdr (q_st q0)) = M_TYPE ->
      dec_stream_strict_fuel fs0 (br_stream (q_br q0))
        (ob_slice (q_ob q0) 0 (o_put (q_ob q0))) = Some (X0, rem0) ->
      zlen X0 <= q_out q0 ->
      bs_pack c q0 X0 rem0) ->
  (length (br_stream (q_br q)) <= n')%nat ->
  br_wf (q_br q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  q_ret q = 0 ->
  br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
  inf_iter k13 c q = Some q3 ->
  (length (br_stream (q_br q3)) < length (br_stream (q_br q)))%nat ->
  br_wf (q_br q3) ->
  0 <= o_put (q_ob q3) ->
  0 <= o_left (q_ob q3) ->
  o_put (q_ob q3) + o_left (q_ob q3) = o_put (q_ob q) + o_left (q_ob q) ->
  h_mode (s_hdr (q_st q3)) = M_TYPE ->
  0 <= h_last (s_hdr (q_st q3)) < 2 ->
  q_ret q3 = q_ret q -> q_in q3 = q_in q -> q_out q3 = q_out q ->
  h_wrap (s_hdr (q_st q3)) = h_wrap (s_hdr (q_st q)) ->
  w_wsize (s_win (q_st q3)) = w_wsize (s_win (q_st q)) ->
  w_whave (s_win (q_st q3)) = w_whave (s_win (q_st q)) ->
  t_sane (s_tab (q_st q3)) = t_sane (s_tab (q_st q)) ->
  h_flags (s_hdr (q_st q3)) = h_flags (s_hdr (q_st q)) ->
  h_check (s_hdr (q_st q3)) = h_check (s_hdr (q_st q)) ->
  h_total (s_hdr (q_st q3)) = h_total (s_hdr (q_st q)) ->
  W2Stream.br_haligned (q_br q3) ->
  (if Z.eqb (h_last (s_hdr (q_st q3))) 1
   then X = ob_slice (q_ob q3) 0 (o_put (q_ob q3))
        /\ rem = br_stream (q_br q3)
   else dec_stream_strict_fuel f (br_stream (q_br q3))
          (ob_slice (q_ob q3) 0 (o_put (q_ob q3))) = Some (X, rem)) ->
  zlen X <= q_out q ->
  bs_pack c q X rem.
Proof.
  intros n' f c q k13 q3 X rem IH Hn Hwf0 Htie Hcap Hwh0 Hsn0 Hrt0 Hbud0
         HI13 Hshort Hwf3 Hput3 Hleft3 Hsum3 Hm3 Hlb3 Hret3 Hin3 Hout3
         Hwr3 Hws3 Hwh3 Hsn3 Hfl3 Hck3 Hto3 Hha3 HFIN HX.
  assert (Hbud3 : br_have (q_br q3) + br_bits (q_br q3) / 8 <= 4294967290).
  { pose proof (br_budget_mono (q_br q) (q_br q3) Hwf0 Hwf3
                  ltac:(lia)) as HBM. lia. }
  destruct (Z.eqb_spec (h_last (s_hdr (q_st q3))) 1) as [E|N].
  - destruct HFIN as (HXv & HRv).
    exists k13, q3.
    split. { exact HI13. }
    split. { exact (eq_sym HRv). }
    split. { exact (eq_sym HXv). }
    split. { exact Hwf3. }
    split. { exact Hput3. }
    split. { exact Hleft3. }
    split. { exact Hsum3. }
    split. { exact Hm3. }
    split. { rewrite E. discriminate. }
    split. { exact Hret3. }
    split. { exact Hin3. }
    split. { exact Hout3. }
    split. { exact Hwr3. }
    split. { exact Hfl3. }
    split. { exact Hws3. }
    split. { exact Hwh3. }
    split. { exact Hsn3. }
    split. { exact Hha3. }
    split. { exact Hbud3. }
    split. { exact Hck3. }
    exact Hto3.
  - assert (E0 : h_last (s_hdr (q_st q3)) = 0) by lia.
    cbv iota in HFIN.
    assert (Hentry3 : zr_body_entry q3).
    { split; [exact Hwf3|]. split; [exact Hput3|]. split; [exact Hleft3|].
      split; [rewrite Hout3, Hsum3; exact Htie|].
      split; [rewrite Hout3; exact Hcap|].
      split; [rewrite Hwh3; exact Hwh0|].
      split; [rewrite Hsn3; exact Hsn0|].
      split; [rewrite Hret3; exact Hrt0|].
      split; [exact E0|].
      split; [exact Hha3|].
      exact Hbud3. }
    destruct (IH q3 f X rem ltac:(lia) Hentry3 Hm3 HFIN
                ltac:(rewrite Hout3; exact HX))
      as (k2 & q4 & HI2 & HR2 & HX2 & Hwf4 & Hput4 & Hleft4 & Hsum4
          & Hm4 & Hl4 & Hret4 & Hin4 & Hout4 & Hwr4 & Hfl4 & Hws4
          & Hwh4 & Hsn4 & Hha4 & Hbud4 & Hck4 & Hto4).
    exists (k13 + k2)%nat, q4.
    split. { rewrite (inf_iter_add k13 k2 c q q3 HI13). exact HI2. }
    split. { exact HR2. }
    split. { exact HX2. }
    split. { exact Hwf4. }
    split. { exact Hput4. }
    split. { exact Hleft4. }
    split. { rewrite Hsum4. exact Hsum3. }
    split. { exact Hm4. }
    split. { exact Hl4. }
    split. { rewrite Hret4. exact Hret3. }
    split. { rewrite Hin4. exact Hin3. }
    split. { rewrite Hout4. exact Hout3. }
    split. { rewrite Hwr4. exact Hwr3. }
    split. { rewrite Hfl4. exact Hfl3. }
    split. { rewrite Hws4. exact Hws3. }
    split. { rewrite Hwh4. exact Hwh3. }
    split. { rewrite Hsn4. exact Hsn3. }
    split. { exact Hha4. }
    split. { exact Hbud4. }
    split. { rewrite Hck4. exact Hck3. }
    rewrite Hto4. exact Hto3.
Qed.

(** One block, good-only, parameterised by the TYPEDO source (the two
    entries of the walk share it). *)
Lemma bs_blocks : forall (n' fs : nat) c q qsrc X rem,
  zr_cflush_ok c ->
  (forall q0 (fs0 : nat) X0 rem0,
      (length (br_stream (q_br q0)) < n')%nat ->
      zr_body_entry q0 ->
      h_mode (s_hdr (q_st q0)) = M_TYPE ->
      dec_stream_strict_fuel fs0 (br_stream (q_br q0))
        (ob_slice (q_ob q0) 0 (o_put (q_ob q0))) = Some (X0, rem0) ->
      zlen X0 <= q_out q0 ->
      bs_pack c q0 X0 rem0) ->
  (length (br_stream (q_br q)) <= n')%nat ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  q_ret q = 0 ->
  W2Stream.br_haligned (q_br q) ->
  br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
  dec_stream_strict_fuel fs (br_stream (q_br q))
    (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some (X, rem) ->
  zlen X <= q_out q ->
  inf_step c q = inf_TYPEDO c qsrc ->
  q_br qsrc = q_br q ->
  q_ob qsrc = q_ob q ->
  q_ret qsrc = q_ret q ->
  q_in qsrc = q_in q ->
  q_out qsrc = q_out q ->
  h_last (s_hdr (q_st qsrc)) = 0 ->
  h_wrap (s_hdr (q_st qsrc)) = h_wrap (s_hdr (q_st q)) ->
  w_wsize (s_win (q_st qsrc)) = w_wsize (s_win (q_st q)) ->
  w_whave (s_win (q_st qsrc)) = w_whave (s_win (q_st q)) ->
  t_sane (s_tab (q_st qsrc)) = t_sane (s_tab (q_st q)) ->
  h_flags (s_hdr (q_st qsrc)) = h_flags (s_hdr (q_st q)) ->
  h_check (s_hdr (q_st qsrc)) = h_check (s_hdr (q_st q)) ->
  h_total (s_hdr (q_st qsrc)) = h_total (s_hdr (q_st q)) ->
  bs_pack c q X rem.
Proof.
  intros n' fs c q qsrc X rem Hc IH Hn Hwf Hput Hleft Htie Hcap Hwh Hsn
         Hrt0 Hha Hbud HDX HX HSTEP Hbr Hob Hrt Hin Hout Hl0 Hwr Hws
         Hwhs Hsns Hfls Hcks Htos.
  assert (HFl : n_flush c <> Z_TREES) by (destruct Hc as [_ HT]; exact HT).
  assert (Hwfs : br_wf (q_br qsrc)) by (rewrite Hbr; exact Hwf).
  destruct fs as [|f]; [discriminate HDX|].
  cbn [dec_stream_strict_fuel] in HDX.
  destruct (dec_blk_strict (br_stream (q_br q))
              (ob_slice (q_ob q) 0 (o_put (q_ob q))))
    as [[[fin out1] rem1]|] eqn:SD; [|discriminate HDX].
  pose proof (dec_blk_strict_weaken _ _ _ _ _ SD) as SDW.
  pose proof (dec_blk_shorter _ _ _ _ _ SDW) as Hshort1.
  destruct (bs_blk_extract _ _ _ _ _ SD)
    as (bfinal & btype & r1 & r2 & E1 & E2 & EFIN & ARMS).
  pose proof (read_bits_bound _ _ _ _ E1) as HBb.
  change (2 ^ Z.of_nat 1) with 2 in HBb.
  pose proof (read_bits_length _ _ _ _ E1) as HL1.
  pose proof (read_bits_length _ _ _ _ E2) as HL2.
  assert (Hout1X : zlen out1 <= zlen X).
  { pose proof HDX as HDX2. destruct fin.
    - injection HDX2 as EX ER. rewrite EX. lia.
    - pose proof (bs_zlen_mono _ _ _ _ _ HDX2). lia. }
  assert (H3b : (3 <= length (br_stream (q_br qsrc)))%nat)
    by (rewrite Hbr; lia).
  destruct (bs_typedo_cont c qsrc HFl Hl0 Hwfs H3b) as (q1 & ET).
  assert (HI1 : inf_iter 1 c q = Some q1)
    by (apply inf_iter_one; rewrite HSTEP; exact ET).
  destruct (zr_typedo_sound_plus c qsrc q1 HFl Hl0 Hwfs ET) as
    [ (HBAD & HN) | (lastb & ty & r1' & R1m & R2m & HLast1 & Hwf1
                     & HQF & HArm) ].
  { exfalso.
    specialize (HN (ob_slice (q_ob q) 0 (o_put (q_ob q)))).
    rewrite Hbr in HN. rewrite SDW in HN. discriminate. }
  rewrite Hbr in R1m.
  rewrite E1 in R1m. injection R1m as EL1 ER1. subst lastb r1'.
  rewrite E2 in R2m. injection R2m as ET1 ES1. subst ty.
  destruct HQF as (HOb1 & HIn1 & HOut1 & HRet1 & HWs1).
  rewrite Hob in HOb1. rewrite Hin in HIn1. rewrite Hout in HOut1.
  rewrite Hrt in HRet1. rewrite Hws in HWs1.
  destruct (zr_typedo_ride c qsrc q1 ET)
    as (HWr1 & HWh1 & HSn1 & HFl1 & HCk1 & HTo1).
  rewrite Hwr in HWr1. rewrite Hwhs in HWh1. rewrite Hsns in HSn1.
  rewrite Hfls in HFl1. rewrite Hcks in HCk1. rewrite Htos in HTo1.
  assert (Hhas : W2Stream.br_haligned (q_br qsrc))
    by (rewrite Hbr; exact Hha).
  assert (Hha1 : W2Stream.br_haligned (q_br q1))
    by (exact (zr_typedo_reader c qsrc q1 Hl0 Hwfs ET Hhas)).
  assert (HlenT : (length (br_stream (q_br q1))
                   <= length (br_stream (q_br q)))%nat)
    by (rewrite <- ES1; lia).
  assert (Hbud1 : br_have (q_br q1) + br_bits (q_br q1) / 8
                  <= 4294967290).
  { pose proof (br_budget_mono (q_br q) (q_br q1) Hwf Hwf1 HlenT) as HBM.
    lia. }
  assert (Hput1 : 0 <= o_put (q_ob q1)) by (rewrite HOb1; exact Hput).
  assert (Hleft1 : 0 <= o_left (q_ob q1)) by (rewrite HOb1; exact Hleft).
  assert (Htie1 : q_out q1 = o_put (q_ob q1) + o_left (q_ob q1))
    by (rewrite HOut1, HOb1; exact Htie).
  assert (Hcap1 : q_out q1 <= 4294967295) by (rewrite HOut1; exact Hcap).
  assert (Hwh1' : w_whave (s_win (q_st q1)) = 0)
    by (rewrite HWh1; exact Hwh).
  assert (Hsn1' : t_sane (s_tab (q_st q1)) <> 0)
    by (rewrite HSn1; exact Hsn).
  assert (Hrt1 : q_ret q1 = 0) by (rewrite HRet1; exact Hrt0).
  assert (HSl1 : ob_slice (q_ob q1) 0 (o_put (q_ob q1))
                 = ob_slice (q_ob q) 0 (o_put (q_ob q)))
    by (rewrite HOb1; reflexivity).
  destruct ARMS as [ (HT0 & payload & HDs & HOUT)
                   | [ (HT1 & syms & HDsym & HRz)
                     | (HT2 & lit & dst & r3 & syms & HDD & HDsym & HRz) ] ].
  - (* ---- stored ---- *)
    destruct HArm as [ (Hty & Hm1) | [ (Hty & _) | (Hty & _) ] ];
      try (rewrite HT0 in Hty; discriminate Hty).
    rewrite ES1 in HDs.
    assert (LS : zlen out1 = o_put (q_ob q) + zlen payload).
    { rewrite HOUT. unfold zlen. rewrite length_app, Nat2Z.inj_add.
      rewrite zr_slice_length, Z2Nat.id by exact Hput. reflexivity. }
    assert (Hroom1 : zlen payload <= o_left (q_ob q1))
      by (rewrite HOb1; lia).
    destruct (bs_stored_trip_good c q1 payload rem1 Hc Hwf1 Hput1 Hleft1
                Hm1 HDs Hroom1)
      as (k1 & q3 & HI3 & HS3 & Hwf3 & HSl3 & Hsum3 & Hput3 & Hleft3
          & Hm3 & Hl3 & Hret3 & Hin3 & Hout3 & Hwr3 & Hws3 & Hwh3
          & Hsn3 & Hfl3 & Hck3 & Hto3 & Hha3).
    apply (bs_close n' f c q (1 + k1)%nat q3 X rem IH Hn Hwf Htie Hcap
             Hwh Hsn Hrt0 Hbud).
    + rewrite (inf_iter_add 1 k1 c q q1 HI1). exact HI3.
    + rewrite HS3. exact Hshort1.
    + exact Hwf3.
    + exact Hput3.
    + exact Hleft3.
    + rewrite Hsum3, HOb1. reflexivity.
    + exact Hm3.
    + rewrite Hl3, HLast1. exact HBb.
    + rewrite Hret3. exact HRet1.
    + rewrite Hin3. exact HIn1.
    + rewrite Hout3. exact HOut1.
    + rewrite Hwr3. exact HWr1.
    + rewrite Hws3. exact HWs1.
    + rewrite Hwh3. exact HWh1.
    + rewrite Hsn3. exact HSn1.
    + rewrite Hfl3. exact HFl1.
    + rewrite Hck3. exact HCk1.
    + rewrite Hto3. exact HTo1.
    + exact Hha3.
    + rewrite Hl3, HLast1, <- EFIN.
      destruct fin.
      * pose proof HDX as HDX2. injection HDX2 as EX ER.
        split.
        { rewrite <- EX, HOUT, HSl3, HSl1. reflexivity. }
        { rewrite <- ER. exact (eq_sym HS3). }
      * rewrite HS3, HSl3, HSl1, <- HOUT. exact HDX.
    + exact HX.
  - (* ---- fixed ---- *)
    destruct HArm as [ (Hty & _) | [ (Hty & Hm1 & HtL & HtLb & HtD & HtDb)
                     | (Hty & _) ] ];
      try (rewrite HT1 in Hty; discriminate Hty).
    rewrite ES1 in HDsym.
    assert (HRz1 : resolve_lz syms (ob_slice (q_ob q1) 0 (o_put (q_ob q1)))
                   = Some out1)
      by (rewrite HSl1; exact HRz).
    assert (Hroom1 : zlen out1 <= q_out q1) by (rewrite HOut1; lia).
    destruct (k2_fixed_leg_good c q1 syms rem1 out1 Hc Hwf1 Hha1 Hbud1
                Hput1 Hleft1 Htie1 Hcap1 Hwh1' Hsn1' Hm1 HtL HtLb HtD HtDb
                HDsym HRz1 Hroom1)
      as (k1 & q3 & HI3 & HS3 & Hwf3 & HSl3 & Hsum3 & Hput3 & Hleft3
          & Hm3 & Hl3 & HBF3 & Hha3 & Hbud3k).
    destruct HBF3
      as (Hin3 & Hout3 & Hret3 & Hws3 & Hwr3 & Hfl3 & Hck3 & Hto3
          & Hwh3 & Hsn3).
    apply (bs_close n' f c q (1 + k1)%nat q3 X rem IH Hn Hwf Htie Hcap
             Hwh Hsn Hrt0 Hbud).
    + rewrite (inf_iter_add 1 k1 c q q1 HI1). exact HI3.
    + rewrite HS3. exact Hshort1.
    + exact Hwf3.
    + exact Hput3.
    + exact Hleft3.
    + rewrite Hsum3, HOb1. reflexivity.
    + exact Hm3.
    + rewrite Hl3, HLast1. exact HBb.
    + rewrite Hret3. exact HRet1.
    + rewrite Hin3. exact HIn1.
    + rewrite Hout3. exact HOut1.
    + rewrite Hwr3. exact HWr1.
    + rewrite Hws3. exact HWs1.
    + rewrite Hwh3. exact HWh1.
    + rewrite Hsn3. exact HSn1.
    + rewrite Hfl3. exact HFl1.
    + rewrite Hck3. exact HCk1.
    + rewrite Hto3. exact HTo1.
    + exact Hha3.
    + rewrite Hl3, HLast1, <- EFIN.
      destruct fin.
      * pose proof HDX as HDX2. injection HDX2 as EX ER.
        split; [ rewrite <- EX; exact (eq_sym HSl3)
               | rewrite <- ER; exact (eq_sym HS3) ].
      * rewrite HS3, HSl3. exact HDX.
    + exact HX.
  - (* ---- dynamic ---- *)
    destruct HArm as [ (Hty & _) | [ (Hty & _) | (Hty & Hm1) ] ];
      try (rewrite HT2 in Hty; discriminate Hty).
    rewrite ES1 in HDD.
    destruct (bs_dec_256 _ _ _ _ _ HDsym) as (cw & H256).
    assert (HRz1 : resolve_lz syms (ob_slice (q_ob q1) 0 (o_put (q_ob q1)))
                   = Some out1)
      by (rewrite HSl1; exact HRz).
    assert (Hroom1 : zlen out1 <= q_out q1) by (rewrite HOut1; lia).
    destruct (k3_dyn_leg_good c q1 lit dst r3 syms rem1 out1 Hc Hwf1 Hha1
                Hbud1 Hput1 Hleft1 Htie1 Hcap1 Hwh1' Hsn1' Hrt1 Hm1 HDD
                (ex_intro _ cw H256) HDsym HRz1 Hroom1)
      as (k1 & q3 & HI3 & HS3 & Hwf3 & HSl3 & Hsum3 & Hput3 & Hleft3
          & Hm3 & Hl3 & HBF3 & Hha3 & Hbud3k).
    destruct HBF3
      as (Hin3 & Hout3 & Hret3 & Hws3 & Hwr3 & Hfl3 & Hck3 & Hto3
          & Hwh3 & Hsn3).
    apply (bs_close n' f c q (1 + k1)%nat q3 X rem IH Hn Hwf Htie Hcap
             Hwh Hsn Hrt0 Hbud).
    + rewrite (inf_iter_add 1 k1 c q q1 HI1). exact HI3.
    + rewrite HS3. exact Hshort1.
    + exact Hwf3.
    + exact Hput3.
    + exact Hleft3.
    + rewrite Hsum3, HOb1. reflexivity.
    + exact Hm3.
    + rewrite Hl3, HLast1. exact HBb.
    + rewrite Hret3. exact HRet1.
    + rewrite Hin3. exact HIn1.
    + rewrite Hout3. exact HOut1.
    + rewrite Hwr3. exact HWr1.
    + rewrite Hws3. exact HWs1.
    + rewrite Hwh3. exact HWh1.
    + rewrite Hsn3. exact HSn1.
    + rewrite Hfl3. exact HFl1.
    + rewrite Hck3. exact HCk1.
    + rewrite Hto3. exact HTo1.
    + exact Hha3.
    + rewrite Hl3, HLast1, <- EFIN.
      destruct fin.
      * pose proof HDX as HDX2. injection HDX2 as EX ER.
        split; [ rewrite <- EX; exact (eq_sym HSl3)
               | rewrite <- ER; exact (eq_sym HS3) ].
      * rewrite HS3, HSl3. exact HDX.
    + exact HX.
Qed.

(** The fuel walk. *)
Lemma bs_walk : forall n (fs : nat) c q X rem,
  zr_cflush_ok c ->
  (length (br_stream (q_br q)) < n)%nat ->
  zr_body_entry q ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  dec_stream_strict_fuel fs (br_stream (q_br q))
    (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some (X, rem) ->
  zlen X <= q_out q ->
  bs_pack c q X rem.
Proof.
  induction n as [|n' IHn]; intros fs c q X rem Hc Hn Hentry Hm HDX HX;
    [lia|].
  destruct Hentry
    as (Hwf & Hput & Hleft & Htie & Hcap & Hwh & Hsn & Hrt0 & Hlast
        & Hha & Hbud).
  apply (bs_blocks n' fs c q q X rem Hc).
  - intros q0 fs0 X0 rem0 Hf He0 Hm0 HD0 HX0.
    exact (IHn fs0 c q0 X0 rem0 Hc Hf He0 Hm0 HD0 HX0).
  - lia.
  - exact Hwf.
  - exact Hput.
  - exact Hleft.
  - exact Htie.
  - exact Hcap.
  - exact Hwh.
  - exact Hsn.
  - exact Hrt0.
  - exact Hha.
  - exact Hbud.
  - exact HDX.
  - exact HX.
  - exact (zr_step_at_type c q Hc Hm).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hlast.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Ladder (b): the fueled head. *)
Theorem zr_body_select_fuel_holds : ZrBodySelectFuel_STMT.
Proof.
  intros n c q X rem Hc Hn Hentry Hm HDX HX.
  exact (bs_walk n (S (length (br_stream (q_br q)))) c q X rem Hc Hn
           Hentry Hm HDX HX).
Qed.

(** Ladder (c), half 1: the frozen M_TYPE head. *)
Theorem zr_body_select_holds : ZrBodySelect.
Proof.
  intros c q X rem Hc Hentry Hm HDX HX.
  exact (bs_walk (S (length (br_stream (q_br q))))
           (S (length (br_stream (q_br q)))) c q X rem Hc
           (Nat.lt_succ_diag_r _) Hentry Hm HDX HX).
Qed.

(** Ladder (c), half 2: the frozen raw-lane wrap-0 M_HEAD head. *)
Theorem zr_body_select_head0_holds : ZrBodySelectHead0.
Proof.
  intros c q X rem Hc Hentry Hm Hw HDX HX.
  pose proof Hentry as (Hwf & Hput & Hleft & Htie & Hcap & Hwh & Hsn
                        & Hrt0 & Hlast & Hha & Hbud).
  assert (PACK : bs_pack c q X rem).
  { apply (bs_blocks (length (br_stream (q_br q)))
             (S (length (br_stream (q_br q)))) c q (qmode q M_TYPEDO)
             X rem Hc).
    - intros q0 fs0 X0 rem0 Hf He0 Hm0 HD0 HX0.
      exact (bs_walk (S (length (br_stream (q_br q0)))) fs0 c q0 X0 rem0
               Hc (Nat.lt_succ_diag_r _) He0 Hm0 HD0 HX0).
    - exact (Nat.le_refl _).
    - exact Hwf.
    - exact Hput.
    - exact Hleft.
    - exact Htie.
    - exact Hcap.
    - exact Hwh.
    - exact Hsn.
    - exact Hrt0.
    - exact Hha.
    - exact Hbud.
    - exact HDX.
    - exact HX.
    - exact (zr_step_at_head0 c q Hm Hw).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hlast.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  destruct PACK as (k & q' & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9
                    & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18
                    & C19 & C20 & C21).
  exists k, q'.
  split. { exact C1. }
  split. { exact C2. }
  split. { exact C3. }
  split. { exact C4. }
  split. { exact C5. }
  split. { exact C6. }
  split. { exact C7. }
  split. { exact C8. }
  split. { exact C9. }
  split. { exact C10. }
  split. { exact C11. }
  split. { exact C12. }
  split. { exact C13. }
  split. { exact C14. }
  split. { exact C15. }
  split. { exact C16. }
  split. { exact C17. }
  split. { exact C18. }
  exact C19.
Qed.

Set Printing Width 2000.
Print Assumptions zr_body_select_fuel_holds.
Print Assumptions zr_body_select_holds.
Print Assumptions zr_body_select_head0_holds.
