(** * Bridge.DMatch.MLm3 — group M: pair D20, [longest_match] whole.

    S5's [longest_match] returns the state with [match_start] set at the
    last hit and the length; RT's returns the length and the start.  Under
    [lz_rel] and [geom_rel] the lengths agree and S5's state is related to
    RT's window state with [match_start := ] RT's start.  The caller's
    facts: [strstart] has room for a full match ([strstart + 262 <= 65536],
    what [fill_window] leaves), the candidate is a real earlier position,
    and the hash chains point below [strstart] (group R's [ms_chain_ok],
    after the caller's [insert_string]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MLm1 MLm2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

Lemma m_chain_range : forall level, 1 <= level <= 9 -> 4 <= RC.cfg_max_chain level <= 4096.
Proof.
  intros level Hl.
  assert (Hc : level = 1 \/ level = 2 \/ level = 3 \/ level = 4 \/ level = 5
               \/ level = 6 \/ level = 7 \/ level = 8 \/ level = 9) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]; vm_compute; split; discriminate.
Qed.

Theorem m_longest_match : forall s t cm,
  lz_rel s t -> geom_rel s t -> s5_geom s -> cfg_facts (RD.d_cfg t) ->
  1 <= RC.dg_level (RD.d_cfg t) <= 9 ->
  RD.ls_windowsize (RD.d_ls t) = 65536 ->
  1 <= RD.ls_strstart (RD.d_ls t) -> RD.ls_strstart (RD.d_ls t) + 262 <= 65536 ->
  1 <= cm < RD.ls_strstart (RD.d_ls t) ->
  0 <= RD.ls_prevlen (RD.d_ls t) <= 258 ->
  (forall i, 0 <= i < 32768 ->
     0 <= RD.ls_prev (RD.d_ls t) i
     /\ (RD.ls_prev (RD.d_ls t) i = 0 \/ RD.ls_prev (RD.d_ls t) i < RD.ls_strstart (RD.d_ls t))) ->
  snd (SLz.longest_match s cm) = fst (RD.longest_match (RD.d_cfg t) (RD.d_ls t) cm)
  /\ lz_rel (fst (SLz.longest_match s cm))
            (RD.setD_ls (RD.setL_matchstart (snd (RD.longest_match (RD.d_cfg t) (RD.d_ls t) cm)) (RD.d_ls t)) t)
  /\ nonlz_view (fst (SLz.longest_match s cm)) = nonlz_view s.
Proof.
  intros s t cm Hl Hgr Hg Hc Hlev Hws Hss1 Hss2 Hcm Hpl Hprev.
  set (l := RD.d_ls t) in *. set (g := RD.d_cfg t) in *.
  pose proof (m_chain_range (RC.dg_level g) Hlev) as Hch.
  assert (Ecm : RC.dg_max_chain_length g = RC.cfg_max_chain (RC.dg_level g)) by (destruct Hc; assumption).
  unfold geom_rel in Hgr. cbv zeta in Hgr.
  destruct Hgr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgood & _ & Hnice & Hmaxc & _).
  fold g in Hgood, Hnice, Hmaxc.
  pose proof (lzr_ss _ _ Hl) as Ess. pose proof (lzr_pl _ _ Hl) as Epl. pose proof (lzr_la _ _ Hl) as Ela.
  pose proof (lzr_win _ _ Hl) as Hrw. fold l in Ess, Epl, Ela, Hrw. rewrite Hws in Hrw.
  unfold SLz.longest_match, RD.longest_match. cbv zeta.
  rewrite Hmaxc, Hgood, Hnice, Ess, Epl, Ela, (sg_w_size _ Hg).
  change DS.MIN_LOOKAHEAD with 262. change DS.NIL with 0. change RD.NIL with 0.
  rewrite (cf_max_dist _ Hc). change (32768 - 262) with 32506.
  rewrite (Hrw (RD.ls_strstart l + RD.ls_prevlen l - 1)), (Hrw (RD.ls_strstart l + RD.ls_prevlen l)) by lia.
  set (chain0 := if RC.dg_good_match g <=? RD.ls_prevlen l
                 then Z.shiftr (RC.dg_max_chain_length g) 2 else RC.dg_max_chain_length g).
  assert (Hc0 : 1 <= chain0 <= 4096).
  { subst chain0. rewrite Ecm. destruct (RC.dg_good_match g <=? RD.ls_prevlen l); [|lia].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
    split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
  assert (Hc1 : chain0 <= RC.dg_max_chain_length g).
  { subst chain0. destruct (RC.dg_good_match g <=? RD.ls_prevlen l); [|lia].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply Z.div_le_upper_bound; lia. }
  set (nice := if RD.ls_lookahead l <? RC.dg_nice_match g then RD.ls_lookahead l else RC.dg_nice_match g).
  set (limit := if 32506 <? RD.ls_strstart l then RD.ls_strstart l - 32506 else 0).
  set (c := {| RD.x_win := RD.ls_window l; RD.x_prev := RD.ls_prev l; RD.x_scan := RD.ls_strstart l;
               RD.x_nice := nice; RD.x_limit := limit; RD.x_wmask := RC.dg_w_mask g |}).
  set (st0 := {| RD.m_cur := cm; RD.m_best := RD.ls_prevlen l; RD.m_start := RD.ls_matchstart l;
                 RD.m_end1 := RD.ls_window l (RD.ls_strstart l + RD.ls_prevlen l - 1);
                 RD.m_end := RD.ls_window l (RD.ls_strstart l + RD.ls_prevlen l);
                 RD.m_chain := chain0 |}).
  assert (HL0 : lzm t s (RD.m_start st0)) by exact Hl.
  assert (P1 : 1 <= RD.m_cur st0 < RD.ls_strstart l) by exact Hcm.
  assert (P2 : 0 <= RD.m_best st0 <= 258) by exact Hpl.
  assert (P3 : 1 <= RD.m_chain st0 <= Z.of_nat (Z.to_nat chain0)) by (cbn [RD.m_chain st0]; lia).
  assert (P4 : RD.m_chain st0 < Z.of_nat (Z.to_nat (RC.dg_max_chain_length g) + 2)) by (cbn [RD.m_chain st0]; lia).
  assert (P5 : RD.m_chain st0 <= 4096) by (cbn [RD.m_chain st0]; lia).
  assert (Hlim : 0 <= limit) by (subst limit; destruct (Z.ltb_spec 32506 (RD.ls_strstart l)); lia).
  destruct (m_lm_loop t c nice limit eq_refl eq_refl eq_refl eq_refl eq_refl (cf_w_mask _ Hc) Hws
              (conj Hss1 Hss2) Hlim Hprev
              (Z.to_nat chain0) (Z.to_nat (RC.dg_max_chain_length g) + 2) s st0 HL0 Hg P1 P2 P3 P4 P5)
    as (R1 & R2 & R3).
  cbv zeta in R1, R2, R3. cbn [RD.m_cur RD.m_best RD.m_chain RD.m_end1 RD.m_end st0] in R1, R2, R3.
  destruct (SLz.longest_match_loop (Z.to_nat chain0) s cm chain0 (RD.ls_prevlen l) nice limit
              (RD.ls_window l (RD.ls_strstart l + RD.ls_prevlen l - 1))
              (RD.ls_window l (RD.ls_strstart l + RD.ls_prevlen l))) as [s' best] eqn:EL.
  cbn [fst snd] in R1, R2, R3.
  unfold lzm in R2. pose proof (lzr_la _ _ R2) as Ela'.
  cbn [RD.d_ls RD.setD_ls RD.setL_matchstart RD.ls_lookahead] in Ela'. fold l in Ela'.
  rewrite Ela', R1.
  destruct (RD.m_best (RD.lm_loop (Z.to_nat (RC.dg_max_chain_length g) + 2) c st0) <=? RD.ls_lookahead l);
    cbn [fst snd]; (split; [reflexivity|]); (split; [exact R2 | exact R3]).
Qed.
