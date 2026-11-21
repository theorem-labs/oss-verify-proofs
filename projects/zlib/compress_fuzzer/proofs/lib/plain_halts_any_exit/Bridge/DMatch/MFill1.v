(** * Bridge.DMatch.MFill1 — group M: pair D17b, [fill_window]'s pieces.

    One trip of [fill_window]'s loop is, in both models: a window slide when
    [strstart] has reached [w_size + MAX_DIST] ([s5_pre] / [rt_pre]), a stop
    when there is no input, a [read_buf] into the window after the
    lookahead ([MReadBuf]), the lookahead bump, and the hash re-seed over
    the [insert] pending strings ([s5_seed] / [RD.fw_seed]).  This file
    proves each piece on [lz_rel]; [MFill2] assembles the trip and the loop.

    - [m_fw_insert]: S5's [fill_window_insert] (fuel exactly [insert]) is
      RT's [fw_insert] (fuel [insert + 1], stops at [insert = 0]).
    - [m_seed]: the re-seed.
    - [m_slide]: the slide (window move, [match_start] mod 2^32,
      [strstart] / [block_start] down by [w_size], [insert] clamp,
      [slide_hash]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

Ltac lz_destr H :=
  unfold lz_rel in H; cbv zeta in H;
  destruct H as (Hlw & Hlp & Hlh & Hrw & Hrp & Hrh & Hwsz & Hih & Hbs & Hml & Hpm & Hma & Hss & Hms
                 & Hla & Hpl & Hin & Hhw).

Ltac rt_ls :=
  cbn [RD.d_ls RD.setD_ls RD.setD_strm RD.setL_window RD.setL_prev RD.setL_head RD.setL_insh
       RD.setL_blockstart RD.setL_matchlen RD.setL_prevmatch RD.setL_matchavail RD.setL_strstart
       RD.setL_matchstart RD.setL_lookahead RD.setL_prevlen RD.setL_insert RD.setL_highwater
       RD.setL_windowsize
       RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch
       RD.ls_matchavail RD.ls_strstart RD.ls_matchstart RD.ls_lookahead RD.ls_prevlen RD.ls_insert
       RD.ls_highwater RD.ls_windowsize].

(* ------------------------------------------------------------------------- *)
(* 1.  The insert loop                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma m_s5_fwi_S : forall f s str,
  SLz.fill_window_insert (S f) s str
  = if negb (Z.eqb (DS.ds_insert s) 0) then
      let s1 := DS.set_insert (fst (SLz.insert_string s str)) (DS.ds_insert s - 1) in
      if Z.ltb (DS.ds_lookahead s1 + DS.ds_insert s1) DS.MIN_MATCH then s1
      else SLz.fill_window_insert f s1 (str + 1)
    else s.
Proof. reflexivity. Qed.

Lemma m_rt_fwi_S : forall f g str l,
  RD.fw_insert (S f) g str l
  = if Z.eqb (RD.ls_insert l) 0 then l
    else
      let l4 := RD.setL_insert (RD.ls_insert l - 1) (snd (RD.insert_string g str l)) in
      if Z.ltb (RD.ls_lookahead l4 + RD.ls_insert l4) RC.MIN_MATCH then l4
      else RD.fw_insert f g (str + 1) l4.
Proof. reflexivity. Qed.

(** The RT fields the insert loop leaves alone. *)
Definition ins_frame (l l' : RD.LSt) : Prop :=
  RD.ls_window l' = RD.ls_window l /\ RD.ls_blockstart l' = RD.ls_blockstart l
  /\ RD.ls_matchlen l' = RD.ls_matchlen l /\ RD.ls_prevmatch l' = RD.ls_prevmatch l
  /\ RD.ls_matchavail l' = RD.ls_matchavail l /\ RD.ls_strstart l' = RD.ls_strstart l
  /\ RD.ls_matchstart l' = RD.ls_matchstart l /\ RD.ls_lookahead l' = RD.ls_lookahead l
  /\ RD.ls_prevlen l' = RD.ls_prevlen l /\ RD.ls_highwater l' = RD.ls_highwater l
  /\ RD.ls_windowsize l' = RD.ls_windowsize l
  /\ 0 <= RD.ls_insert l' <= RD.ls_insert l.

Lemma m_set_insert_lz : forall s t v,
  lz_rel s t -> lz_rel (DS.set_insert s v) (RD.setD_ls (RD.setL_insert v (RD.d_ls t)) t).
Proof.
  intros s t v H. lz_destr H. unfold lz_rel. cbv zeta. autorewrite with s5f_insert. rt_ls.
  repeat split; assumption.
Qed.

Theorem m_fw_insert : forall n m s t str,
  lz_rel s t -> s5_geom s -> cfg_facts (RD.d_cfg t) -> RD.ls_windowsize (RD.d_ls t) = 65536 ->
  0 <= RD.ls_insert (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t) ->
  RD.ls_strstart (RD.d_ls t) + RD.ls_lookahead (RD.d_ls t) <= 65536 ->
  (RD.ls_insert (RD.d_ls t) = 0 \/ 3 <= RD.ls_lookahead (RD.d_ls t) + RD.ls_insert (RD.d_ls t)) ->
  RD.ls_insert (RD.d_ls t) <= Z.of_nat n -> RD.ls_insert (RD.d_ls t) < Z.of_nat m ->
  str = RD.ls_strstart (RD.d_ls t) - RD.ls_insert (RD.d_ls t) ->
  lz_rel (SLz.fill_window_insert n s str)
         (RD.setD_ls (RD.fw_insert m (RD.d_cfg t) str (RD.d_ls t)) t)
  /\ nonlz_view (SLz.fill_window_insert n s str) = nonlz_view s
  /\ ins_frame (RD.d_ls t) (RD.fw_insert m (RD.d_cfg t) str (RD.d_ls t)).
Proof.
  induction n as [|n IH]; intros m s t str Hl Hg Hc Hws Hins Hroom Hgo Hn Hm Hstr.
  - (* insert is 0: both stop *)
    assert (Hi0 : RD.ls_insert (RD.d_ls t) = 0) by lia.
    destruct m as [|m]; [lia|]. rewrite m_rt_fwi_S. rewrite Hi0. cbn [Z.eqb].
    cbn [SLz.fill_window_insert].
    replace (RD.setD_ls (RD.d_ls t) t) with t by (destruct t; reflexivity).
    split; [exact Hl|]. split; [reflexivity|].
    unfold ins_frame. rewrite Hi0. repeat split; lia.
  - destruct m as [|m]; [lia|]. rewrite m_s5_fwi_S, m_rt_fwi_S.
    assert (Hii : DS.ds_insert s = RD.ls_insert (RD.d_ls t))
      by (pose proof Hl as H'; lz_destr H'; exact Hin).
    rewrite Hii.
    destruct (Z.eqb_spec (RD.ls_insert (RD.d_ls t)) 0) as [E|E]; cbn [negb].
    + replace (RD.setD_ls (RD.d_ls t) t) with t by (destruct t; reflexivity).
      split; [exact Hl|]. split; [reflexivity|].
      unfold ins_frame. repeat split; lia.
    + destruct Hgo as [Hgo|Hgo]; [contradiction|].
      destruct (m_insert_string s t str Hl Hg Hc Hws ltac:(lia) ltac:(lia)) as (_ & Hl1 & Hv1).
      cbv zeta.
      set (s1 := DS.set_insert (fst (SLz.insert_string s str)) (RD.ls_insert (RD.d_ls t) - 1)).
      set (l1 := RD.setL_insert (RD.ls_insert (RD.d_ls t) - 1)
                   (snd (RD.insert_string (RD.d_cfg t) str (RD.d_ls t)))).
      assert (Hl2 : lz_rel s1 (RD.setD_ls l1 t)).
      { pose proof (m_set_insert_lz _ _ (RD.ls_insert (RD.d_ls t) - 1) Hl1) as H.
        exact H. }
      assert (Hv2 : nonlz_view s1 = nonlz_view s) by (exact Hv1).
      (* the two models' stop tests agree *)
      assert (Hla1 : DS.ds_lookahead s1 = RD.ls_lookahead l1)
        by (pose proof Hl2 as H'; lz_destr H'; exact Hla).
      assert (Hin1 : DS.ds_insert s1 = RD.ls_insert l1)
        by (pose proof Hl2 as H'; lz_destr H'; exact Hin).
      rewrite Hla1, Hin1. unfold DS.MIN_MATCH. change RC.MIN_MATCH with 3.
      (* RT facts of l1 *)
      assert (Hf1 : RD.ls_insert l1 = RD.ls_insert (RD.d_ls t) - 1
                    /\ RD.ls_lookahead l1 = RD.ls_lookahead (RD.d_ls t)
                    /\ RD.ls_strstart l1 = RD.ls_strstart (RD.d_ls t)
                    /\ RD.ls_windowsize l1 = RD.ls_windowsize (RD.d_ls t)
                    /\ ins_frame (RD.d_ls t) l1).
      { subst l1. unfold RD.insert_string. cbv zeta. cbn [snd]. rt_ls.
        unfold ins_frame. rt_ls. repeat split; lia. }
      destruct Hf1 as (Hi1 & Hla1' & Hss1 & Hws1 & Hfr1).
      destruct (Z.ltb_spec (RD.ls_lookahead l1 + RD.ls_insert l1) 3) as [Lt|Ge].
      * split; [exact Hl2|]. split; [exact Hv2|]. exact Hfr1.
      * assert (Hs5g : s5_geom s1) by (destruct Hg; constructor; assumption).
        assert (P1 : cfg_facts (RD.d_cfg (RD.setD_ls l1 t))) by exact Hc.
        assert (P2 : RD.ls_windowsize (RD.d_ls (RD.setD_ls l1 t)) = 65536)
          by (cbn [RD.d_ls RD.setD_ls]; lia).
        assert (P3 : 0 <= RD.ls_insert (RD.d_ls (RD.setD_ls l1 t)) <= RD.ls_strstart (RD.d_ls (RD.setD_ls l1 t)))
          by (cbn [RD.d_ls RD.setD_ls]; lia).
        assert (P4 : RD.ls_strstart (RD.d_ls (RD.setD_ls l1 t)) + RD.ls_lookahead (RD.d_ls (RD.setD_ls l1 t)) <= 65536)
          by (cbn [RD.d_ls RD.setD_ls]; lia).
        assert (P5 : RD.ls_insert (RD.d_ls (RD.setD_ls l1 t)) = 0
                     \/ 3 <= RD.ls_lookahead (RD.d_ls (RD.setD_ls l1 t)) + RD.ls_insert (RD.d_ls (RD.setD_ls l1 t)))
          by (cbn [RD.d_ls RD.setD_ls]; lia).
        assert (P6 : RD.ls_insert (RD.d_ls (RD.setD_ls l1 t)) <= Z.of_nat n) by (cbn [RD.d_ls RD.setD_ls]; lia).
        assert (P7 : RD.ls_insert (RD.d_ls (RD.setD_ls l1 t)) < Z.of_nat m) by (cbn [RD.d_ls RD.setD_ls]; lia).
        assert (P8 : str + 1 = RD.ls_strstart (RD.d_ls (RD.setD_ls l1 t)) - RD.ls_insert (RD.d_ls (RD.setD_ls l1 t)))
          by (cbn [RD.d_ls RD.setD_ls]; lia).
        destruct (IH m s1 (RD.setD_ls l1 t) (str + 1) Hl2 Hs5g P1 P2 P3 P4 P5 P6 P7 P8) as (IH1 & IH2 & IH3).
        cbn [RD.d_ls RD.d_cfg RD.setD_ls] in IH1, IH2, IH3.
        replace (RD.setD_ls (RD.fw_insert m (RD.d_cfg t) (str + 1) l1) (RD.setD_ls l1 t))
          with (RD.setD_ls (RD.fw_insert m (RD.d_cfg t) (str + 1) l1) t) in IH1
          by (destruct t; reflexivity).
        split; [exact IH1|]. split; [rewrite IH2; exact Hv2|].
        destruct Hfr1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
        destruct IH3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
        unfold ins_frame. repeat split; congruence || lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The re-seed                                                           *)
(* ------------------------------------------------------------------------- *)

Definition s5_seed (s : DS.deflate_state) : DS.deflate_state :=
  if Z.leb DS.MIN_MATCH (DS.ds_lookahead s + DS.ds_insert s) then
    let str := DS.ds_strstart s - DS.ds_insert s in
    let s := DS.set_ins_h s (arr_get (DS.ds_window s) str) in
    let s := DS.set_ins_h s (SLz.update_hash s (DS.ds_ins_h s) (arr_get (DS.ds_window s) (str + 1))) in
    SLz.fill_window_insert (Z.to_nat (DS.ds_insert s)) s str
  else s.

Lemma m_set_ins_h_lz : forall s t v,
  lz_rel s t -> lz_rel (DS.set_ins_h s v) (RD.setD_ls (RD.setL_insh v (RD.d_ls t)) t).
Proof.
  intros s t v H. lz_destr H. unfold lz_rel. cbv zeta. autorewrite with s5f_ins_h. rt_ls.
  repeat split; assumption.
Qed.

Theorem m_seed : forall s t,
  lz_rel s t -> s5_geom s -> cfg_facts (RD.d_cfg t) -> RD.ls_windowsize (RD.d_ls t) = 65536 ->
  0 <= RD.ls_insert (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t) ->
  0 <= RD.ls_lookahead (RD.d_ls t) ->
  RD.ls_strstart (RD.d_ls t) + RD.ls_lookahead (RD.d_ls t) <= 65536 ->
  lz_rel (s5_seed s) (RD.setD_ls (RD.fw_seed (RD.d_cfg t) (RD.d_ls t)) t)
  /\ nonlz_view (s5_seed s) = nonlz_view s
  /\ ins_frame (RD.d_ls t) (RD.fw_seed (RD.d_cfg t) (RD.d_ls t)).
Proof.
  intros s t Hl Hg Hc Hws Hins Hla0 Hroom.
  pose proof Hl as H'. lz_destr H'.
  unfold s5_seed, RD.fw_seed. rewrite Hla, Hin. unfold DS.MIN_MATCH. change RC.MIN_MATCH with 3.
  destruct (Z.leb_spec 3 (RD.ls_lookahead (RD.d_ls t) + RD.ls_insert (RD.d_ls t))) as [Go|No].
  - cbv zeta. rewrite ?Hss, ?Hin.
    set (str := RD.ls_strstart (RD.d_ls t) - RD.ls_insert (RD.d_ls t)).
    assert (Hw0 : arr_get (DS.ds_window s) str = RD.ls_window (RD.d_ls t) str) by (apply Hrw; lia).
    assert (Hw1 : arr_get (DS.ds_window s) (str + 1) = RD.ls_window (RD.d_ls t) (str + 1))
      by (apply Hrw; lia).
    autorewrite with s5f_ins_h. rewrite ?Hin, ?Hw0, ?Hw1.
    destruct Hg as [G1 G2 G3 G4 G5 G6 G7].
    rewrite (m_update_hash _ (RD.d_cfg t))
      by (autorewrite with s5f_ins_h; destruct Hc; congruence).
    set (h1 := RD.update_hash (RD.d_cfg t) (RD.ls_window (RD.d_ls t) str) (RD.ls_window (RD.d_ls t) (str + 1))).
    set (s2 := DS.set_ins_h (DS.set_ins_h s (RD.ls_window (RD.d_ls t) str)) h1).
    set (t2 := RD.setD_ls (RD.setL_insh h1 (RD.d_ls t)) t).
    assert (Hl2 : lz_rel s2 t2).
    { pose proof (m_set_ins_h_lz s t (RD.ls_window (RD.d_ls t) str) Hl) as H1.
      pose proof (m_set_ins_h_lz _ _ h1 H1) as H2. exact H2. }
    assert (Hs2g : s5_geom s2) by (constructor; assumption).
    assert (P1 : cfg_facts (RD.d_cfg t2)) by exact Hc.
    assert (P2 : RD.ls_windowsize (RD.d_ls t2) = 65536) by exact Hws.
    assert (P3 : 0 <= RD.ls_insert (RD.d_ls t2) <= RD.ls_strstart (RD.d_ls t2)) by exact Hins.
    assert (P4 : RD.ls_strstart (RD.d_ls t2) + RD.ls_lookahead (RD.d_ls t2) <= 65536) by exact Hroom.
    assert (P5 : RD.ls_insert (RD.d_ls t2) = 0 \/ 3 <= RD.ls_lookahead (RD.d_ls t2) + RD.ls_insert (RD.d_ls t2))
      by (right; exact Go).
    assert (P6 : RD.ls_insert (RD.d_ls t2) <= Z.of_nat (Z.to_nat (RD.ls_insert (RD.d_ls t)))) by (cbn; lia).
    assert (P7 : RD.ls_insert (RD.d_ls t2) < Z.of_nat (Z.to_nat (RD.ls_insert (RD.d_ls t)) + 1)) by (cbn; lia).
    assert (P8 : str = RD.ls_strstart (RD.d_ls t2) - RD.ls_insert (RD.d_ls t2)) by reflexivity.
    destruct (m_fw_insert _ _ s2 t2 str Hl2 Hs2g P1 P2 P3 P4 P5 P6 P7 P8) as (R1 & R2 & R3).
    subst t2. cbn [RD.d_ls RD.d_cfg RD.setD_ls] in R1, R2, R3.
    replace (RD.setD_ls (RD.fw_insert (Z.to_nat (RD.ls_insert (RD.d_ls t)) + 1) (RD.d_cfg t) str
                           (RD.setL_insh h1 (RD.d_ls t))) (RD.setD_ls (RD.setL_insh h1 (RD.d_ls t)) t))
      with (RD.setD_ls (RD.fw_insert (Z.to_nat (RD.ls_insert (RD.d_ls t)) + 1) (RD.d_cfg t) str
                           (RD.setL_insh h1 (RD.d_ls t))) t) in R1 by (destruct t; reflexivity).
    assert (Hi2 : DS.ds_insert s2 = RD.ls_insert (RD.d_ls t)) by exact Hin.
    try fold s2. rewrite ?Hi2.
    split; [exact R1|]. split; [rewrite R2; reflexivity|].
    destruct R3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    cbn [RD.setL_insh RD.ls_window RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch RD.ls_matchavail
         RD.ls_strstart RD.ls_matchstart RD.ls_lookahead RD.ls_prevlen RD.ls_highwater RD.ls_windowsize
         RD.ls_insert] in *.
    unfold ins_frame. repeat split; congruence || lia.
  - replace (RD.setD_ls (RD.d_ls t) t) with t by (destruct t; reflexivity).
    split; [exact Hl|]. split; [reflexivity|]. unfold ins_frame. repeat split; lia.
Qed.
