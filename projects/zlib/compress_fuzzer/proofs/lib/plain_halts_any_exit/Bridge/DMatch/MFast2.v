(** * Bridge.DMatch.MFast2 — group M: pair D14, the hash insert and match search
    of a [deflate_fast] trip.

    [s5_fast_l1 s] is S5's state after [deflate_fast_body]'s
    [insert_string] / [longest_match] / [set_match_length] (the body after
    the top-of-trip fill); group R's [df_l1 p0] is RT's window state at the
    same point.  [m_fast_l1] relates them.  The insert's [hash_head] is a
    head entry, which group R's [ms_chain_ok] puts at NIL or below
    [strstart]; that makes S5's [wrap32 (strstart - hash_head)] exact and
    gives [longest_match] its candidate range.  [rt_ins_facts] is the RT
    side of [insert_string]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MLm3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

(** RT's [insert_string], field by field. *)
Lemma rt_ins_facts : forall g str l,
  RC.dg_hash_mask g = 32767 -> RC.dg_w_mask g = 32767 ->
  let r := RD.insert_string g str l in
  let h := RD.update_hash g (RD.ls_insh l) (RD.ls_window l (str + RC.MIN_MATCH - 1)) in
  fst r = RD.ls_head l h /\ 0 <= h < 32768
  /\ RD.ls_prev (snd r) = Base.zset (RD.ls_prev l) (Z.land str 32767) (RD.ls_head l h)
  /\ RD.ls_head (snd r) = Base.zset (RD.ls_head l) h (Base.u16 str)
  /\ RD.ls_window (snd r) = RD.ls_window l /\ RD.ls_strstart (snd r) = RD.ls_strstart l
  /\ RD.ls_lookahead (snd r) = RD.ls_lookahead l /\ RD.ls_matchlen (snd r) = RD.ls_matchlen l
  /\ RD.ls_prevlen (snd r) = RD.ls_prevlen l /\ RD.ls_matchstart (snd r) = RD.ls_matchstart l
  /\ RD.ls_prevmatch (snd r) = RD.ls_prevmatch l /\ RD.ls_matchavail (snd r) = RD.ls_matchavail l
  /\ RD.ls_blockstart (snd r) = RD.ls_blockstart l /\ RD.ls_insert (snd r) = RD.ls_insert l
  /\ RD.ls_highwater (snd r) = RD.ls_highwater l /\ RD.ls_windowsize (snd r) = RD.ls_windowsize l.
Proof.
  intros g str l Hhm Hwm r h. subst r h. unfold RD.insert_string. cbv zeta. cbn [fst snd]. rt_ls.
  rewrite Hwm. split; [reflexivity|]. split; [apply m_update_hash_range; exact Hhm|].
  repeat split; reflexivity.
Qed.

(** The chain facts after an insert at [strstart]: the new [prev] entry is
    the old head, NIL or below [strstart]. *)
Lemma rt_ins_prev_ok : forall g l,
  cfg_facts g -> RK.ms_chain_ok g l ->
  let r := RD.insert_string g (RD.ls_strstart l) l in
  0 <= fst r /\ (fst r = 0 \/ fst r < RD.ls_strstart l)
  /\ (forall i, 0 <= i < 32768 ->
        0 <= RD.ls_prev (snd r) i /\ (RD.ls_prev (snd r) i = 0 \/ RD.ls_prev (snd r) i < RD.ls_strstart l)).
Proof.
  intros g l Hc [Hhd Hpv] r.
  destruct (rt_ins_facts g (RD.ls_strstart l) l (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
    as (E1 & Hh & E2 & _).
  subst r. rewrite E1, E2.
  rewrite (cf_hash_size _ Hc) in Hhd. rewrite (cf_w_size _ Hc) in Hpv.
  destruct (Hhd _ Hh) as [H0 H1]. unfold RD.NIL in H1.
  split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold Base.zset. destruct (Z.eqb i _); [split; assumption|].
  destruct (Hpv i Hi) as [P0 P1]. unfold RD.NIL in P1. split; assumption.
Qed.

Lemma mt_ws : forall t, mt_inv t -> RD.ls_windowsize (RD.d_ls t) = 65536.
Proof.
  intros t H. rewrite (RK.mi_winsize _ (mt_ms t H)), (cf_w_size _ (m_cfg_facts t H)). reflexivity.
Qed.

Definition s5_fast_l1 (s : DS.deflate_state) : DS.deflate_state :=
  let '(s, hash_head) :=
    if Z.leb DS.MIN_MATCH (DS.ds_lookahead s) then SLz.insert_string s (DS.ds_strstart s) else (s, DS.NIL) in
  if negb (Z.eqb hash_head DS.NIL)
     && Z.leb (wrap32 (DS.ds_strstart s - hash_head)) (DS.ds_w_size s - DS.MIN_LOOKAHEAD)
  then let '(s, ml) := SLz.longest_match s hash_head in DS.set_match_length s ml
  else s.

Theorem m_fast_l1 : forall s p0 po pi,
  dst_rel s p0 po pi -> mt_inv p0 ->
  RD.ls_strstart (RD.d_ls p0) + 262 <= 65536 -> 1 <= RC.dg_level (RD.d_cfg p0) ->
  lz_rel (s5_fast_l1 s) (RD.setD_ls (RK.df_l1 p0) p0)
  /\ nonlz_view (s5_fast_l1 s) = nonlz_view s.
Proof.
  intros s p0 po pi Hd Hm Hroom Hlev1.
  pose proof Hd as Hd'. apply m_dst_split in Hd' as [Hl Hn].
  pose proof (m_cfg_facts p0 Hm) as Hc.
  pose proof (m_s5_geom s p0 (proj1 Hd) Hm) as Hg.
  pose proof (mt_ms p0 Hm) as Hms.
  pose proof (RK.mi_chain _ Hms) as Hch. pose proof (RK.mi_str _ Hms) as Hss0.
  pose proof (mt_level p0 Hm) as Hlev.
  pose proof (mt_ml p0 Hm) as Hml.
  pose proof (lzr_la _ _ Hl) as Ela. pose proof (lzr_ss _ _ Hl) as Ess.
  unfold s5_fast_l1, RK.df_l1. rewrite Ela, Ess. change DS.MIN_MATCH with RC.MIN_MATCH. cbv zeta.
  destruct (Z.leb_spec RC.MIN_MATCH (RD.ls_lookahead (RD.d_ls p0))) as [Ins|NoIns].
  - (* insert at strstart *)
    pose proof (mt_ws p0 Hm) as Hws.
    destruct (m_insert_string s p0 (RD.ls_strstart (RD.d_ls p0)) Hl Hg Hc Hws
                ltac:(apply (RK.mi_str _ Hms)) ltac:(lia)) as (I1 & I2 & I3).
    destruct (rt_ins_prev_ok (RD.d_cfg p0) (RD.d_ls p0) Hc Hch) as (H0 & H1 & Hpv0).
    destruct (rt_ins_facts (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)
                (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
      as (_ & _ & _ & _ & Jw & Jss & Jla & Jml & Jpl & Jms & Jpm & Jma & Jbs & Jins & Jhw & Jws).
    destruct (SLz.insert_string s (RD.ls_strstart (RD.d_ls p0))) as [s1 hh] eqn:EI.
    destruct (RD.insert_string (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)) as [hh' l0] eqn:ER.
    try (rewrite ER in *).
    cbn [fst snd] in I1, I2, I3, H0, H1, Hpv0, Jw, Jss, Jla, Jml, Jpl, Jws. subst hh'.
    pose proof (lzr_ss _ _ I2) as Ess1. cbn [RD.d_ls RD.setD_ls] in Ess1. rewrite Jss in Ess1.
    assert (Hg1 : s5_geom s1) by (exact (MFill3.m_geom_nonlz s s1 I3 Hg)).
    cbn [fst snd]. rewrite Ess1, (sg_w_size _ Hg1), Jss. change DS.NIL with RD.NIL.
    rewrite (cf_max_dist _ Hc). change (32768 - DS.MIN_LOOKAHEAD) with 32506.
    rewrite (wrap32_id (RD.ls_strstart (RD.d_ls p0) - hh)) by (unfold RD.NIL in *; mpow; lia).
    destruct (negb (hh =? RD.NIL) && (RD.ls_strstart (RD.d_ls p0) - hh <=? 32506)) eqn:EC.
    + (* search the chain *)
      apply andb_prop in EC as [EC1 EC2]. apply negb_true_iff, Z.eqb_neq in EC1. unfold RD.NIL in EC1.
      set (t1 := RD.setD_ls l0 p0).
      assert (Hgr1 : geom_rel s1 t1).
      { pose proof (m_nl_frame s s1 p0 l0 po pi I3 Hn) as N. destruct N; assumption. }
      assert (P1 : 1 <= RC.dg_level (RD.d_cfg t1) <= 9) by (subst t1; cbn; lia).
      assert (P2 : RD.ls_windowsize (RD.d_ls t1) = 65536) by (subst t1; cbn; rewrite Jws; exact Hws).
      assert (P3 : 1 <= RD.ls_strstart (RD.d_ls t1)) by (subst t1; cbn; rewrite Jss; lia).
      assert (P4 : RD.ls_strstart (RD.d_ls t1) + 262 <= 65536) by (subst t1; cbn; rewrite Jss; lia).
      assert (P5 : 1 <= hh < RD.ls_strstart (RD.d_ls t1)) by (subst t1; cbn; rewrite Jss; lia).
      assert (P6 : 0 <= RD.ls_prevlen (RD.d_ls t1) <= 258) by (subst t1; cbn; rewrite Jpl; lia).
      assert (P7 : forall i, 0 <= i < 32768 ->
                0 <= RD.ls_prev (RD.d_ls t1) i
                /\ (RD.ls_prev (RD.d_ls t1) i = 0 \/ RD.ls_prev (RD.d_ls t1) i < RD.ls_strstart (RD.d_ls t1)))
        by (subst t1; cbn; rewrite Jss; exact Hpv0).
      destruct (m_longest_match s1 t1 hh I2 Hgr1 Hg1 Hc P1 P2 P3 P4 P5 P6 P7) as (L1 & L2 & L3).
      subst t1. cbn [RD.d_ls RD.d_cfg RD.setD_ls] in L1, L2, L3. rewrite rt_setD_ls_ls in L2.
      destruct (SLz.longest_match s1 hh) as [s2 ml] eqn:EL. cbn [fst snd] in L1, L2, L3.
      split.
      * exact (lz_set_match_length s2 p0 _ ml (fst (RD.longest_match (RD.d_cfg p0) l0 hh)) L2 L1).
      * rewrite <- I3, <- L3. reflexivity.
    + split; [exact I2 | exact I3].
  - (* no insert: hash_head is NIL *)
    cbn [fst snd]. unfold DS.NIL, RD.NIL. cbn [Z.eqb negb andb].
    split; [rewrite rt_setD_ls_eta; exact Hl | reflexivity].
Qed.
