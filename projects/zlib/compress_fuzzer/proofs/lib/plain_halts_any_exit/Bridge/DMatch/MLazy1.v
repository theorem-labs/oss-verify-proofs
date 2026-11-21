(** * Bridge.DMatch.MLazy1 — group M: pair D15, the hash insert and lazy match
    search of a [deflate_slow] trip.

    [s5_slow_l2 s] is S5's state after [deflate_slow_body]'s
    [insert_string], the [prev_length] / [prev_match] / [match_length]
    updates, [longest_match] and the short-far-match filter; group R's
    [ds_l2 p0] is RT's window state at the same point.  Both are cut after
    the insert ([s5_slow_rest] / [rt_slow_rest]); [m_slow_rest] relates the
    rests and [m_slow_l2] the whole.  S5 reads the filter's distance as
    [wrap32 (strstart - match_start)]: exact, because the match start is a
    chain position or the old one, both at most [strstart] and no further
    back than the consumed input ([mt_slid]).  [rt_ds_l2_facts] is RT's
    window state after the search, field by field. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MLm3 MFast2 MFast3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

(* ------------------------------------------------------------------------- *)
(* 1.  Both searches, cut after the insert                                   *)
(* ------------------------------------------------------------------------- *)

Definition s5_slow_rest (s : DS.deflate_state) (hash_head : Z) : DS.deflate_state :=
  let s := DS.set_prev_length s (DS.ds_match_length s) in
  let s := DS.set_prev_match s (DS.ds_match_start s) in
  let s := DS.set_match_length s (DS.MIN_MATCH - 1) in
  if negb (Z.eqb hash_head DS.NIL) && Z.ltb (DS.ds_prev_length s) (DS.ds_max_lazy_match s)
     && Z.leb (wrap32 (DS.ds_strstart s - hash_head)) (DS.ds_w_size s - DS.MIN_LOOKAHEAD)
  then
    let '(s, ml) := SLz.longest_match s hash_head in
    let s := DS.set_match_length s ml in
    if Z.leb (DS.ds_match_length s) 5
       && (Z.eqb (DS.ds_strategy s) Z_FILTERED
           || (Z.eqb (DS.ds_match_length s) DS.MIN_MATCH
               && Z.ltb DS.TOO_FAR (wrap32 (DS.ds_strstart s - DS.ds_match_start s))))
    then DS.set_match_length s (DS.MIN_MATCH - 1)
    else s
  else s.

Definition s5_slow_l2 (s : DS.deflate_state) : DS.deflate_state :=
  let '(s, hash_head) :=
    if Z.leb DS.MIN_MATCH (DS.ds_lookahead s) then SLz.insert_string s (DS.ds_strstart s) else (s, DS.NIL) in
  s5_slow_rest s hash_head.

Definition rt_slow_rest (g : RC.DeflGeom) (l0 : RD.LSt) (hash_head : Z) : RD.LSt :=
  let l1 := RD.setL_matchlen (RC.MIN_MATCH - 1)
              (RD.setL_prevmatch (RD.ls_matchstart l0) (RD.setL_prevlen (RD.ls_matchlen l0) l0)) in
  if negb (Z.eqb hash_head RD.NIL)
     && (Z.ltb (RD.ls_prevlen l1) (RC.dg_max_lazy_match g))
     && (Z.leb (RD.ls_strstart l1 - hash_head) (RC.dg_max_dist g)) then
    let r := RD.longest_match g l1 hash_head in
    let l1a := RD.setL_matchstart (snd r) (RD.setL_matchlen (fst r) l1) in
    if (Z.leb (RD.ls_matchlen l1a) 5)
       && ((Z.eqb (RC.dg_strategy g) RT.Z_FILTERED)
           || ((Z.eqb (RD.ls_matchlen l1a) RC.MIN_MATCH)
               && (Z.ltb RD.TOO_FAR (RD.ls_strstart l1a - RD.ls_matchstart l1a))))
    then RD.setL_matchlen (RC.MIN_MATCH - 1) l1a else l1a
  else l1.

Lemma rt_ds_l2_shape : forall p0,
  RK.ds_l2 p0
  = let ph := if Z.leb RC.MIN_MATCH (RD.ls_lookahead (RD.d_ls p0))
              then RD.insert_string (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)
              else (RD.NIL, RD.d_ls p0) in
    rt_slow_rest (RD.d_cfg p0) (snd ph) (fst ph).
Proof. intros p0. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  RT's search, field by field                                           *)
(* ------------------------------------------------------------------------- *)

Lemma rt_slow_rest_facts : forall g l0 hh,
  RC.dg_w_mask g = 32767 -> RC.dg_max_dist g = 32506 ->
  (hh = 0 \/ 1 <= hh < RD.ls_strstart l0) -> 0 <= RD.ls_matchlen l0 <= 258 -> 0 <= RD.ls_lookahead l0 ->
  (forall i, 0 <= i < 32768 -> RD.ls_prev l0 i = 0 \/ RD.ls_prev l0 i < RD.ls_strstart l0) ->
  let l2 := rt_slow_rest g l0 hh in
  RD.ls_window l2 = RD.ls_window l0 /\ RD.ls_strstart l2 = RD.ls_strstart l0
  /\ RD.ls_lookahead l2 = RD.ls_lookahead l0 /\ RD.ls_blockstart l2 = RD.ls_blockstart l0
  /\ RD.ls_highwater l2 = RD.ls_highwater l0 /\ RD.ls_matchavail l2 = RD.ls_matchavail l0
  /\ RD.ls_insert l2 = RD.ls_insert l0 /\ RD.ls_windowsize l2 = RD.ls_windowsize l0
  /\ RD.ls_prevlen l2 = RD.ls_matchlen l0 /\ RD.ls_prevmatch l2 = RD.ls_matchstart l0
  /\ (RD.ls_matchlen l2 = RC.MIN_MATCH - 1
      \/ (0 <= RD.ls_matchlen l2 <= RD.ls_lookahead l0 /\ RD.ls_matchlen l2 <= 258))
  /\ (RD.ls_matchstart l2 = RD.ls_matchstart l0 \/ 1 <= RD.ls_matchstart l2 < RD.ls_strstart l0).
Proof.
  intros g l0 hh Hwm Hmd Hhh Hml Hla Hpv l2. subst l2.
  unfold rt_slow_rest. cbv zeta.
  set (l1 := RD.setL_matchlen (RC.MIN_MATCH - 1)
               (RD.setL_prevmatch (RD.ls_matchstart l0) (RD.setL_prevlen (RD.ls_matchlen l0) l0))).
  destruct (negb (hh =? RD.NIL) && (RD.ls_prevlen l1 <? RC.dg_max_lazy_match g)
            && (RD.ls_strstart l1 - hh <=? RC.dg_max_dist g)) eqn:EC.
  - assert (Hlive : 1 <= hh < RD.ls_strstart l0).
    { destruct Hhh as [E|E]; [|exact E]. subst hh. unfold RD.NIL in EC. cbn [Z.eqb negb andb] in EC.
      discriminate. }
    destruct (rt_lm_facts g l1 hh Hwm Hmd ltac:(subst l1; rt_ls; lia) ltac:(subst l1; rt_ls; lia)
                ltac:(subst l1; rt_ls; lia) ltac:(subst l1; rt_ls; exact Hpv)) as [K1 K2].
    rt_ls.
    match goal with |- context [if ?c then _ else _] => destruct c end; rt_ls;
      (repeat (split; [reflexivity|])); (split; [|exact K2]);
      [left; reflexivity | right; exact K1].
  - subst l1. rt_ls. repeat (split; [reflexivity|]). split; [left; reflexivity | left; reflexivity].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The rests, S5 against RT                                              *)
(* ------------------------------------------------------------------------- *)

Theorem m_slow_rest : forall s1 hh p0 l0 po pi,
  lz_rel s1 (RD.setD_ls l0 p0) -> nl_rel s1 (RD.setD_ls l0 p0) po pi -> cfg_facts (RD.d_cfg p0) ->
  1 <= RC.dg_level (RD.d_cfg p0) <= 9 -> RD.ls_windowsize l0 = 65536 ->
  0 <= RD.ls_strstart l0 -> RD.ls_strstart l0 + 262 <= 65536 ->
  (hh = 0 \/ 1 <= hh < RD.ls_strstart l0) -> 0 <= RD.ls_matchlen l0 <= 258 -> 0 <= RD.ls_lookahead l0 ->
  (forall i, 0 <= i < 32768 ->
     0 <= RD.ls_prev l0 i /\ (RD.ls_prev l0 i = 0 \/ RD.ls_prev l0 i < RD.ls_strstart l0)) ->
  0 <= RD.ls_strstart l0 - RD.ls_matchstart l0 < 2 ^ 32 ->
  lz_rel (s5_slow_rest s1 hh) (RD.setD_ls (rt_slow_rest (RD.d_cfg p0) l0 hh) p0)
  /\ nonlz_view (s5_slow_rest s1 hh) = nonlz_view s1.
Proof.
  intros s1 hh p0 l0 po pi Hl Hn Hc Hlev Hws Hss0 Hroom Hhh Hml Hla Hpv Hmsd.
  pose proof (lzr_ml _ _ Hl) as Eml. pose proof (lzr_ms _ _ Hl) as Ems. pose proof (lzr_ss _ _ Hl) as Ess.
  cbn [RD.d_ls RD.setD_ls] in Eml, Ems, Ess.
  unfold s5_slow_rest, rt_slow_rest. cbv zeta.
  (* the three setters *)
  assert (A1 : lz_rel (DS.set_prev_length s1 (DS.ds_match_length s1))
                      (RD.setD_ls (RD.setL_prevlen (RD.ls_matchlen l0) l0) p0))
    by (apply lz_set_prev_length; [exact Hl | exact Eml]).
  assert (A2 : lz_rel (DS.set_prev_match (DS.set_prev_length s1 (DS.ds_match_length s1))
                         (DS.ds_match_start (DS.set_prev_length s1 (DS.ds_match_length s1))))
                      (RD.setD_ls (RD.setL_prevmatch (RD.ls_matchstart l0)
                                     (RD.setL_prevlen (RD.ls_matchlen l0) l0)) p0))
    by (apply lz_set_prev_match; [exact A1 | exact Ems]).
  assert (A3 : lz_rel (DS.set_match_length (DS.set_prev_match (DS.set_prev_length s1 (DS.ds_match_length s1))
                         (DS.ds_match_start (DS.set_prev_length s1 (DS.ds_match_length s1)))) (DS.MIN_MATCH - 1))
                      (RD.setD_ls (RD.setL_matchlen (RC.MIN_MATCH - 1) (RD.setL_prevmatch (RD.ls_matchstart l0)
                                     (RD.setL_prevlen (RD.ls_matchlen l0) l0))) p0))
    by (apply lz_set_match_length; [exact A2 | reflexivity]).
  set (sc := DS.set_match_length (DS.set_prev_match (DS.set_prev_length s1 (DS.ds_match_length s1))
               (DS.ds_match_start (DS.set_prev_length s1 (DS.ds_match_length s1)))) (DS.MIN_MATCH - 1)) in *.
  set (l1 := RD.setL_matchlen (RC.MIN_MATCH - 1) (RD.setL_prevmatch (RD.ls_matchstart l0)
               (RD.setL_prevlen (RD.ls_matchlen l0) l0))) in *.
  assert (Hvc : nonlz_view sc = nonlz_view s1) by reflexivity.
  pose proof (m_nl_frame s1 sc (RD.setD_ls l0 p0) l1 po pi Hvc Hn) as Hn1. rewrite rt_setD_ls_ls in Hn1.
  assert (Hgr1 : geom_rel sc (RD.setD_ls l1 p0)) by (destruct Hn1; assumption).
  pose proof (MFill3.m_s5_geom_cf sc _ Hgr1 Hc) as Hg1.
  assert (Epl : DS.ds_prev_length sc = RD.ls_prevlen l1) by exact Eml.
  assert (Elz : DS.ds_max_lazy_match sc = RC.dg_max_lazy_match (RD.d_cfg p0))
    by (unfold geom_rel in Hgr1; cbv zeta in Hgr1; tauto).
  assert (Ess1 : DS.ds_strstart sc = RD.ls_strstart l1) by exact Ess.
  destruct Hhh as [E0|Hlive].
  { (* hash_head is NIL: no search *)
    subst hh. unfold DS.NIL, RD.NIL. cbn [Z.eqb negb andb]. split; [exact A3 | exact Hvc]. }
  rewrite Epl, Elz, Ess1, (sg_w_size _ Hg1), (cf_max_dist _ Hc).
  change (32768 - DS.MIN_LOOKAHEAD) with 32506. change DS.NIL with RD.NIL.
  rewrite (wrap32_id (RD.ls_strstart l1 - hh)) by (subst l1; rt_ls; mpow; lia).
  destruct (negb (hh =? RD.NIL) && (RD.ls_prevlen l1 <? RC.dg_max_lazy_match (RD.d_cfg p0))
            && (RD.ls_strstart l1 - hh <=? 32506)); [|split; [exact A3 | exact Hvc]].
  (* search the chain *)
  assert (P1 : 1 <= RC.dg_level (RD.d_cfg (RD.setD_ls l1 p0)) <= 9) by exact Hlev.
  assert (P2 : RD.ls_windowsize (RD.d_ls (RD.setD_ls l1 p0)) = 65536) by exact Hws.
  assert (P3 : 1 <= RD.ls_strstart (RD.d_ls (RD.setD_ls l1 p0))) by (cbn; lia).
  assert (P4 : RD.ls_strstart (RD.d_ls (RD.setD_ls l1 p0)) + 262 <= 65536) by (cbn; lia).
  assert (P5 : 1 <= hh < RD.ls_strstart (RD.d_ls (RD.setD_ls l1 p0))) by (cbn; lia).
  assert (P6 : 0 <= RD.ls_prevlen (RD.d_ls (RD.setD_ls l1 p0)) <= 258) by (cbn; lia).
  assert (P7 : forall i, 0 <= i < 32768 ->
            0 <= RD.ls_prev (RD.d_ls (RD.setD_ls l1 p0)) i
            /\ (RD.ls_prev (RD.d_ls (RD.setD_ls l1 p0)) i = 0
                \/ RD.ls_prev (RD.d_ls (RD.setD_ls l1 p0)) i < RD.ls_strstart (RD.d_ls (RD.setD_ls l1 p0))))
    by exact Hpv.
  destruct (m_longest_match sc (RD.setD_ls l1 p0) hh A3 Hgr1 Hg1 Hc P1 P2 P3 P4 P5 P6 P7) as (L1 & L2 & L3).
  cbn [RD.d_ls RD.d_cfg RD.setD_ls] in L1, L2, L3. rewrite rt_setD_ls_ls in L2.
  destruct (rt_lm_facts (RD.d_cfg p0) l1 hh (cf_w_mask _ Hc) (cf_max_dist _ Hc) ltac:(subst l1; rt_ls; lia)
              ltac:(subst l1; rt_ls; lia) ltac:(subst l1; rt_ls; lia)
              ltac:(subst l1; rt_ls; intros i Hi; destruct (Hpv i Hi) as [_ P]; exact P)) as [K1 K2].
  set (r := RD.longest_match (RD.d_cfg p0) l1 hh) in *.
  destruct (SLz.longest_match sc hh) as [s2 ml] eqn:EL. cbn [fst snd] in L1, L2, L3.
  pose proof (lz_set_match_length s2 p0 _ ml (fst r) L2 L1) as B1. subst ml.
  assert (Hg2 : s5_geom s2) by (exact (MFill3.m_geom_nonlz sc s2 L3 Hg1)).
  pose proof (lzr_ss _ _ L2) as Ess2. pose proof (lzr_ms _ _ L2) as Ems2.
  cbn [RD.d_ls RD.setD_ls RD.setL_matchstart RD.ls_strstart RD.ls_matchstart] in Ess2, Ems2.
  assert (Edist : wrap32 (DS.ds_strstart s2 - DS.ds_match_start s2) = RD.ls_strstart l1 - snd r).
  { rewrite Ess2, Ems2. apply RK.ms_wrap_dist.
    assert (Hs1 : RD.ls_strstart l1 = RD.ls_strstart l0) by reflexivity.
    destruct K2 as [K|K]; [rewrite K; subst l1; rt_ls; exact Hmsd | rewrite Hs1 in K |- *; mpow; lia]. }
  rewrite ds_match_length__set_match_length, ds_strategy__set_match_length, ds_strstart__set_match_length,
    ds_match_start__set_match_length, Edist, (sg_strategy _ Hg2), (cf_strategy _ Hc).
  change DS.MIN_MATCH with RC.MIN_MATCH. change DS.TOO_FAR with RD.TOO_FAR. change Z_FILTERED with RT.Z_FILTERED.
  rt_ls.
  assert (Hv2 : nonlz_view (DS.set_match_length s2 (fst r)) = nonlz_view s1) by (rewrite <- Hvc, <- L3; reflexivity).
  destruct ((fst r <=? 5) && ((0 =? RT.Z_FILTERED) || ((fst r =? RC.MIN_MATCH)
            && (RD.TOO_FAR <? RD.ls_strstart l1 - snd r)))).
  - split.
    + exact (lz_set_match_length _ p0 _ (RC.MIN_MATCH - 1) (RC.MIN_MATCH - 1) B1 eq_refl).
    + rewrite <- Hv2. reflexivity.
  - split; [exact B1 | exact Hv2].
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The whole search                                                      *)
(* ------------------------------------------------------------------------- *)

(** How far back [match_start] may lie: no further than the consumed input. *)
Lemma mt_ms_range : forall t, mt_inv t ->
  0 <= RD.ls_strstart (RD.d_ls t) - RD.ls_matchstart (RD.d_ls t) < 2 ^ 32.
Proof.
  intros t Hm. destruct (mt_slid t Hm) as (slid & Z0 & Z1 & Z2 & Z3 & Z4).
  pose proof (mt_inlen t Hm) as Hin. pose proof (RK.mi_look _ (mt_ms t Hm)) as Hla.
  assert (0 <= Chunk.zlen (RD.zs_in (RD.d_strm t))) by (unfold Chunk.zlen; lia).
  lia.
Qed.

Theorem m_slow_l2 : forall s p0 po pi,
  dst_rel s p0 po pi -> mt_inv p0 ->
  RD.ls_strstart (RD.d_ls p0) + 262 <= 65536 -> 1 <= RC.dg_level (RD.d_cfg p0) ->
  lz_rel (s5_slow_l2 s) (RD.setD_ls (RK.ds_l2 p0) p0)
  /\ nonlz_view (s5_slow_l2 s) = nonlz_view s.
Proof.
  intros s p0 po pi Hd Hm Hroom Hlev1.
  pose proof Hd as Hd'. apply m_dst_split in Hd' as [Hl Hn].
  pose proof (m_cfg_facts p0 Hm) as Hc.
  pose proof (m_s5_geom s p0 (proj1 Hd) Hm) as Hg.
  pose proof (mt_ms p0 Hm) as Hms.
  pose proof (RK.mi_chain _ Hms) as Hch. pose proof (RK.mi_str _ Hms) as Hss0.
  pose proof (RK.mi_look _ Hms) as Hla0.
  pose proof (mt_level p0 Hm) as Hlev.
  pose proof (mt_ml p0 Hm) as Hml.
  pose proof (mt_ws p0 Hm) as Hws.
  pose proof (mt_ms_range p0 Hm) as Hmsd.
  pose proof (lzr_la _ _ Hl) as Ela. pose proof (lzr_ss _ _ Hl) as Ess.
  unfold s5_slow_l2. rewrite rt_ds_l2_shape. cbv zeta. rewrite Ela, Ess.
  change DS.MIN_MATCH with RC.MIN_MATCH.
  destruct (Z.leb_spec RC.MIN_MATCH (RD.ls_lookahead (RD.d_ls p0))) as [Ins|NoIns].
  - (* insert at strstart *)
    destruct (m_insert_string s p0 (RD.ls_strstart (RD.d_ls p0)) Hl Hg Hc Hws Hss0 ltac:(lia)) as (I1 & I2 & I3).
    destruct (rt_ins_prev_ok (RD.d_cfg p0) (RD.d_ls p0) Hc Hch) as (H0 & H1 & Hpv0).
    destruct (rt_ins_facts (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)
                (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
      as (_ & _ & _ & _ & Jw & Jss & Jla & Jml & Jpl & Jms & Jpm & Jma & Jbs & Jins & Jhw & Jws).
    destruct (SLz.insert_string s (RD.ls_strstart (RD.d_ls p0))) as [s1 hh] eqn:EI.
    destruct (RD.insert_string (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)) as [hh' l0] eqn:ER.
    cbn [fst snd] in I1, I2, I3, H0, H1, Hpv0, Jw, Jss, Jla, Jml, Jpl, Jms, Jws. subst hh'.
    pose proof (m_nl_frame s s1 p0 l0 po pi I3 Hn) as Hn1.
    destruct (m_slow_rest s1 hh p0 l0 po pi I2 Hn1 Hc ltac:(lia) ltac:(rewrite Jws; exact Hws)
                ltac:(rewrite Jss; exact Hss0) ltac:(rewrite Jss; lia)
                ltac:(rewrite Jss; destruct (Z.eq_dec hh 0); [left | right]; lia)
                ltac:(rewrite Jml; lia) ltac:(rewrite Jla; lia) ltac:(rewrite Jss; exact Hpv0)
                ltac:(rewrite Jss, Jms; exact Hmsd)) as [R1 R2].
    split; [exact R1 | rewrite R2; exact I3].
  - (* no insert: hash_head is NIL *)
    cbn [fst snd]. change DS.NIL with 0. change RD.NIL with 0.
    assert (Hl0 : lz_rel s (RD.setD_ls (RD.d_ls p0) p0)) by (rewrite rt_setD_ls_eta; exact Hl).
    assert (Hn0 : nl_rel s (RD.setD_ls (RD.d_ls p0) p0) po pi) by (rewrite rt_setD_ls_eta; exact Hn).
    destruct Hch as [_ Hpv]. rewrite (cf_w_size _ Hc) in Hpv. unfold RD.NIL in Hpv.
    exact (m_slow_rest s 0 p0 (RD.d_ls p0) po pi Hl0 Hn0 Hc ltac:(lia) Hws Hss0 ltac:(lia) ltac:(left; reflexivity)
             (proj1 Hml) Hla0 Hpv Hmsd).
Qed.

Lemma rt_ds_l2_facts : forall p0,
  mt_inv p0 ->
  let l := RD.d_ls p0 in
  let l2 := RK.ds_l2 p0 in
  RD.ls_window l2 = RD.ls_window l /\ RD.ls_strstart l2 = RD.ls_strstart l
  /\ RD.ls_lookahead l2 = RD.ls_lookahead l /\ RD.ls_blockstart l2 = RD.ls_blockstart l
  /\ RD.ls_highwater l2 = RD.ls_highwater l /\ RD.ls_matchavail l2 = RD.ls_matchavail l
  /\ RD.ls_insert l2 = RD.ls_insert l /\ RD.ls_windowsize l2 = RD.ls_windowsize l
  /\ RD.ls_prevlen l2 = RD.ls_matchlen l /\ RD.ls_prevmatch l2 = RD.ls_matchstart l
  /\ (RD.ls_matchlen l2 = RC.MIN_MATCH - 1
      \/ (0 <= RD.ls_matchlen l2 <= RD.ls_lookahead l /\ RD.ls_matchlen l2 <= 258))
  /\ (RD.ls_matchstart l2 = RD.ls_matchstart l \/ 1 <= RD.ls_matchstart l2 < RD.ls_strstart l).
Proof.
  intros p0 Hm l l2. subst l l2.
  pose proof (m_cfg_facts p0 Hm) as Hc. pose proof (mt_ms p0 Hm) as Hms.
  pose proof (RK.mi_chain _ Hms) as Hch. pose proof (RK.mi_look _ Hms) as Hla0.
  pose proof (mt_ml p0 Hm) as Hml.
  rewrite rt_ds_l2_shape. cbv zeta.
  destruct (Z.leb RC.MIN_MATCH (RD.ls_lookahead (RD.d_ls p0))).
  - destruct (rt_ins_prev_ok (RD.d_cfg p0) (RD.d_ls p0) Hc Hch) as (H0 & H1 & Hpv0).
    destruct (rt_ins_facts (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)
                (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
      as (_ & _ & _ & _ & Jw & Jss & Jla & Jml & Jpl & Jms & Jpm & Jma & Jbs & Jins & Jhw & Jws).
    set (r := RD.insert_string (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)) in *.
    destruct (rt_slow_rest_facts (RD.d_cfg p0) (snd r) (fst r) (cf_w_mask _ Hc) (cf_max_dist _ Hc)
                ltac:(rewrite Jss; destruct (Z.eq_dec (fst r) 0); [left | right]; lia)
                ltac:(rewrite Jml; lia) ltac:(rewrite Jla; lia)
                ltac:(rewrite Jss; intros i Hi; destruct (Hpv0 i Hi) as [_ P]; exact P))
      as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    rewrite Jw, Jss, Jla, Jbs, Jhw, Jma, Jins, Jws, Jml, Jms in *.
    repeat (split; [assumption|]). assumption.
  - destruct Hch as [_ Hpv]. rewrite (cf_w_size _ Hc) in Hpv. unfold RD.NIL in Hpv.
    cbn [fst snd].
    destruct (rt_slow_rest_facts (RD.d_cfg p0) (RD.d_ls p0) RD.NIL (cf_w_mask _ Hc) (cf_max_dist _ Hc)
                ltac:(left; reflexivity) (proj1 Hml) Hla0 ltac:(intros i Hi; destruct (Hpv i Hi) as [_ P]; exact P))
      as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    repeat (split; [assumption|]). assumption.
Qed.
