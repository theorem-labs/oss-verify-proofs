(** * Bridge.DMatch.MLm2 — group M: pair D20, [longest_match].

    The chain walk in lockstep: S5's 7-tuple loop state
    [(s, best, scan_end1, scan_end, cur_match, chain, cont)] against RT's
    [LmSt] record.  S5 records a hit by setting [match_start] in its state,
    RT in [m_start]; the invariant is [lz_rel s (l with match_start :=
    m_start)].  S5 runs [chain] trips at most, RT [max_chain + 2]; [chain]
    goes down by one on every trip that continues, so one measure bounds
    both.  The byte compare is [MLm1.m_cmp_len]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MLm1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

Section Walk.
  Variables (t : RD.DSt) (c : RD.LmCtx) (nice limit : Z).
  Let l := RD.d_ls t.
  Let ss := RD.ls_strstart l.
  Hypothesis Hc_win : RD.x_win c = RD.ls_window l.
  Hypothesis Hc_prev : RD.x_prev c = RD.ls_prev l.
  Hypothesis Hc_scan : RD.x_scan c = ss.
  Hypothesis Hc_nice : RD.x_nice c = nice.
  Hypothesis Hc_limit : RD.x_limit c = limit.
  Hypothesis Hc_wmask : RD.x_wmask c = 32767.
  Hypothesis Hws : RD.ls_windowsize l = 65536.
  Hypothesis Hss : 1 <= ss /\ ss + 262 <= 65536.
  Hypothesis Hlim : 0 <= limit.
  Hypothesis Hprev : forall i, 0 <= i < 32768 ->
    0 <= RD.ls_prev l i /\ (RD.ls_prev l i = 0 \/ RD.ls_prev l i < ss).

  Definition lzm (s : DS.deflate_state) (ms : Z) : Prop :=
    lz_rel s (RD.setD_ls (RD.setL_matchstart ms l) t).

  Lemma m_lm_loop : forall f fr s st,
    lzm s (RD.m_start st) -> s5_geom s ->
    1 <= RD.m_cur st < ss -> 0 <= RD.m_best st <= 258 ->
    1 <= RD.m_chain st <= Z.of_nat f -> RD.m_chain st < Z.of_nat fr -> RD.m_chain st <= 4096 ->
    let r5 := SLz.longest_match_loop f s (RD.m_cur st) (RD.m_chain st) (RD.m_best st) nice limit
                (RD.m_end1 st) (RD.m_end st) in
    let stf := RD.lm_loop fr c st in
    snd r5 = RD.m_best stf /\ lzm (fst r5) (RD.m_start stf) /\ nonlz_view (fst r5) = nonlz_view s.
  Proof.
    induction f as [|f IH]; intros fr s st HL Hg Hcm Hbest Hch Hfr Hc4 r5 stf; [lia|].
    destruct fr as [|fr]; [lia|].
    subst r5 stf. cbn [SLz.longest_match_loop RD.lm_loop].
    (* the S5 reads, through the relation *)
    assert (Hrd : forall i, 0 <= i < 65536 -> arr_get (DS.ds_window s) i = RD.ls_window l i).
    { intros i Hi. pose proof (lzr_win _ _ HL) as W. cbn [RD.d_ls RD.setD_ls RD.setL_matchstart RD.ls_window
        RD.ls_windowsize] in W. fold l in W. rewrite Hws in W. apply W. exact Hi. }
    assert (Hpv : forall i, 0 <= i < 32768 -> arr_get (DS.ds_prev s) i = RD.ls_prev l i).
    { intros i Hi. pose proof (lzr_prev _ _ HL) as W. cbn [RD.d_ls RD.setD_ls RD.setL_matchstart RD.ls_prev] in W.
      rewrite (sg_w_size _ Hg) in W. apply W. exact Hi. }
    assert (Ess : DS.ds_strstart s = ss).
    { pose proof (lzr_ss _ _ HL) as W. cbn [RD.d_ls RD.setD_ls RD.setL_matchstart RD.ls_strstart] in W. exact W. }
    unfold SLz.longest_match_body. cbv zeta. rewrite Ess.
    rewrite (Hrd (RD.m_cur st + RD.m_best st)), (Hrd (RD.m_cur st + RD.m_best st - 1)), (Hrd (RD.m_cur st)),
      (Hrd ss), (Hrd (RD.m_cur st + 1)), (Hrd (ss + 1)) by lia.
    rewrite (m_cmp_len (DS.ds_window s) (RD.ls_window l) ss (RD.m_cur st))
      by (intros i Hi; split; apply Hrd; lia).
    unfold RD.lm_step, RD.lm_next, RD.lm_hit, RD.lm_len.
    assert (EC : negb (RD.ls_window l (RD.m_cur st + RD.m_best st) =? RD.m_end st)
                 || negb (RD.ls_window l (RD.m_cur st + RD.m_best st - 1) =? RD.m_end1 st)
                 || negb (RD.ls_window l (RD.m_cur st) =? RD.ls_window l ss)
                 || negb (RD.ls_window l (RD.m_cur st + 1) =? RD.ls_window l (ss + 1))
                 = negb (RD.lm_ok c st)).
    { unfold RD.lm_ok. rewrite Hc_win, Hc_scan. rewrite !negb_andb. reflexivity. }
    rewrite EC. rewrite Hc_win, Hc_scan, Hc_prev, Hc_nice, Hc_limit, Hc_wmask.
    change (Z.to_nat RC.MAX_MATCH) with 258%nat.
    set (cm := RD.m_cur st) in *. set (bl := RD.m_best st) in *. set (ch := RD.m_chain st) in *.
    pose proof (m_land_wmask cm) as Hix.
    destruct (Hprev (Z.land cm 32767) Hix) as [Hp0 Hp1].
    set (cm' := RD.ls_prev l (Z.land cm 32767)) in *.
    assert (Hpw : arr_get (DS.ds_prev s) (Z.land cm (DS.ds_w_mask s)) = cm')
      by (rewrite (sg_w_mask _ Hg); apply Hpv; exact Hix).
    destruct (RD.lm_ok c st) eqn:Eok; cbn [negb andb].
    - (* candidate passes the four checks: compare *)
      pose proof (RD.lm_cpl_le 258 (RD.ls_window l) ss cm 3 ltac:(unfold RC.MAX_MATCH; lia)) as Hle.
      set (len := RD.lm_cpl 258 (RD.ls_window l) ss cm 3) in *. change RC.MAX_MATCH with 258 in Hle.
      destruct (Z.ltb_spec bl len) as [Hit|NoHit]; cbn [andb].
      + destruct (Z.leb_spec nice len) as [Nice|NoNice]; cbn [andb].
        * (* hit, long enough: stop *)
          cbn [RD.m_best RD.m_start fst snd].
          split; [reflexivity|]. split; [|reflexivity].
          unfold lzm in *. apply (lz_set_match_start _ t (RD.setL_matchstart (RD.m_start st) l) cm cm) in HL.
          -- exact HL.
          -- rewrite wrap32_id by (mpow; lia). reflexivity.
        * (* hit, keep walking *)
          set (s1 := DS.set_match_start s cm).
          assert (HL1 : lzm s1 cm).
          { unfold lzm in *. apply (lz_set_match_start _ t (RD.setL_matchstart (RD.m_start st) l) cm cm) in HL;
              [exact HL | rewrite wrap32_id by (mpow; lia); reflexivity]. }
          assert (Hg1 : s5_geom s1) by (destruct Hg; constructor; assumption).
          assert (Hpw1 : arr_get (DS.ds_prev s1) (Z.land cm (DS.ds_w_mask s1)) = cm')
            by (subst s1; rewrite ds_prev__set_match_start, ds_w_mask__set_match_start; exact Hpw).
          rewrite Hpw1.
          rewrite (Hrd (ss + len - 1)), (Hrd (ss + len)) by lia.
          cbn [RD.m_cur RD.m_best RD.m_start RD.m_end1 RD.m_end RD.m_chain].
          rewrite (wrap32_id (ch - 1)) by (mpow; lia).
          destruct (Z.ltb_spec limit cm') as [Lc|Lc]; cbn [andb].
          -- destruct (Z.eqb_spec (ch - 1) 0) as [C0|C0]; cbn [negb].
             ++ cbn [RD.m_best RD.m_start fst snd]. split; [reflexivity|]. split; [exact HL1|reflexivity].
             ++ match goal with |- context [RD.lm_loop fr c ?st2] =>
                  destruct (IH fr s1 st2 HL1 Hg1) as (I1 & I2 & I3)
                end.
                all: try (cbn [RD.m_cur RD.m_best RD.m_start RD.m_end1 RD.m_end RD.m_chain] in I1, I2, I3; split; [exact I1|]; split; [exact I2|]; rewrite I3; reflexivity).
                all: cbn [RD.m_cur RD.m_best RD.m_chain]; try lia; destruct Hp1 as [P|P]; lia.
          -- cbn [RD.m_best RD.m_start fst snd]. split; [reflexivity|]. split; [exact HL1|reflexivity].
      + (* no improvement *)
        rewrite Hpw.
        cbn [RD.m_cur RD.m_best RD.m_start RD.m_end1 RD.m_end RD.m_chain].
        change (RD.m_chain st) with ch. change (RD.m_best st) with bl.
        rewrite (wrap32_id (ch - 1)) by (mpow; lia).
        destruct (Z.ltb_spec limit cm') as [Lc|Lc]; cbn [andb].
        * destruct (Z.eqb_spec (ch - 1) 0) as [C0|C0]; cbn [negb].
          -- cbn [fst snd]. split; [reflexivity|]. split; [exact HL|reflexivity].
          -- match goal with |- context [RD.lm_loop fr c ?st2] =>
               destruct (IH fr s st2 HL Hg) as (I1 & I2 & I3)
             end.
             all: try (cbn [RD.m_cur RD.m_best RD.m_start RD.m_end1 RD.m_end RD.m_chain] in I1, I2, I3; split; [exact I1|]; split; [exact I2|]; rewrite I3; reflexivity).
             all: cbn [RD.m_cur RD.m_best RD.m_chain]; try lia; destruct Hp1 as [P|P]; lia.
        * cbn [fst snd]. split; [reflexivity|]. split; [exact HL|reflexivity].
    - (* fails the checks *)
      rewrite Hpw.
      cbn [RD.m_cur RD.m_best RD.m_start RD.m_end1 RD.m_end RD.m_chain].
      change (RD.m_chain st) with ch. change (RD.m_best st) with bl.
      rewrite (wrap32_id (ch - 1)) by (mpow; lia).
      destruct (Z.ltb_spec limit cm') as [Lc|Lc]; cbn [andb].
      + destruct (Z.eqb_spec (ch - 1) 0) as [C0|C0]; cbn [negb].
        * cbn [fst snd]. split; [reflexivity|]. split; [exact HL|reflexivity].
        * match goal with |- context [RD.lm_loop fr c ?st2] =>
            destruct (IH fr s st2 HL Hg) as (I1 & I2 & I3)
          end.
          all: try (cbn [RD.m_cur RD.m_best RD.m_start RD.m_end1 RD.m_end RD.m_chain] in I1, I2, I3; split; [exact I1|]; split; [exact I2|]; rewrite I3; reflexivity).
          all: cbn [RD.m_cur RD.m_best RD.m_chain]; try lia; destruct Hp1 as [P|P]; lia.
      + cbn [fst snd]. split; [reflexivity|]. split; [exact HL|reflexivity].
  Qed.
End Walk.
