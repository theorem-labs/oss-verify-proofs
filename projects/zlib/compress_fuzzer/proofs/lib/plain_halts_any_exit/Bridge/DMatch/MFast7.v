(** * Bridge.DMatch.MFast7 — group M: pair D14, the whole [deflate_fast]
    ([m_deflate_fast]).

    The loop ([m_fast_loop]): S5's [deflate_fast_loop] against RT's
    [df_loop], trip by trip through [MFast6.m_fast_step].  The measure
    [msr = zlen zs_in + lookahead] goes down on every trip that continues,
    and both fuels start above it (S5: [lookahead + avail_in + 1], RT:
    [zlen zs_in + lookahead + 2]), so neither model runs out of fuel.

    The tail ([m_fast_tail]): S5's [set_insert] and [deflate_tail] against
    RT's [ds_tail flush false true]; the flush part ([m_tail_core]) is
    shared with deflate_slow. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require MsDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast1 MFast6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill2 MFill4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.

(* ------------------------------------------------------------------------- *)
(* 1.  The loop                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma msr_nonneg : forall t, mt_inv t -> 0 <= msr t.
Proof.
  intros t Hm. pose proof (RK.mi_look _ (mt_ms t Hm)). unfold msr, Chunk.zlen. lia.
Qed.

Definition floop_rel (po pi : list Z) (r5 : DS.deflate_state * option SLz.block_state)
    (rr : option RD.BlockState * RD.DSt) : Prop :=
  match r5, rr with
  | (s', None), (None, t') => dst_rel s' t' po pi /\ mt_inv t' /\ em_inv s'
  | (s', Some bs), (Some bs', t') =>
      bs_of bs = bs' /\ dst_rel s' t' po pi /\ mt_inv t'
      /\ (DS.cs_avail_out (DS.ds_strm s') <> 0 -> em_inv s')
  | _, _ => False
  end.

Theorem m_fast_loop : forall n m s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_inv s -> 1 <= RC.dg_level (RD.d_cfg t) <= 3 ->
  msr t < Z.of_nat n -> msr t < Z.of_nat m ->
  floop_rel po pi (SBlk.deflate_fast_loop n s flush) (RD.df_loop m flush t).
Proof.
  induction n as [|n IH]; intros m s t po pi flush Hd Hm He Hlev Hn Hmm;
    pose proof (msr_nonneg t Hm) as H0; [lia|].
  destruct m as [|m]; [lia|].
  pose proof (m_fast_step s t po pi flush Hd Hm He Hlev) as Hs.
  cbn [SBlk.deflate_fast_loop RD.df_loop].
  destruct (SBlk.deflate_fast_body s flush) as [s' [| |bs]];
    destruct (RD.df_step flush t) as [t'|bs' t'|t']; cbn [fstep_rel] in Hs; try contradiction.
  - destruct Hs as (H1 & H2 & H3 & H4 & H5).
    apply IH; try assumption; [rewrite H5; exact Hlev | lia | lia].
  - exact Hs.
  - exact Hs.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  mt_inv across the tail                                                *)
(* ------------------------------------------------------------------------- *)

(** A step that changes only [insert], [block_start] (to [strstart]) and
    [match_available] (to 0) of RT's window state keeps [mt_inv]. *)
Lemma mt_inv_lsonly : forall t t',
  mt_inv t -> rt_frame t t' ->
  RD.ls_window (RD.d_ls t') = RD.ls_window (RD.d_ls t) ->
  RD.ls_head (RD.d_ls t') = RD.ls_head (RD.d_ls t) ->
  RD.ls_prev (RD.d_ls t') = RD.ls_prev (RD.d_ls t) ->
  RD.ls_strstart (RD.d_ls t') = RD.ls_strstart (RD.d_ls t) ->
  RD.ls_lookahead (RD.d_ls t') = RD.ls_lookahead (RD.d_ls t) ->
  RD.ls_windowsize (RD.d_ls t') = RD.ls_windowsize (RD.d_ls t) ->
  RD.ls_matchavail (RD.d_ls t') = RD.ls_matchavail (RD.d_ls t) \/ RD.ls_matchavail (RD.d_ls t') = 0 ->
  RD.ls_matchlen (RD.d_ls t') = RD.ls_matchlen (RD.d_ls t) ->
  RD.ls_prevlen (RD.d_ls t') = RD.ls_prevlen (RD.d_ls t) ->
  RD.ls_matchstart (RD.d_ls t') = RD.ls_matchstart (RD.d_ls t) ->
  RD.ls_highwater (RD.d_ls t') = RD.ls_highwater (RD.d_ls t) ->
  0 <= RD.ls_insert (RD.d_ls t') <= RD.ls_strstart (RD.d_ls t') ->
  (RD.ls_blockstart (RD.d_ls t') = RD.ls_blockstart (RD.d_ls t)
   \/ RD.ls_strstart (RD.d_ls t) <= RD.ls_blockstart (RD.d_ls t') <= RD.ls_strstart (RD.d_ls t')) ->
  mt_inv t'.
Proof.
  intros t t' Hm FR Ew Eh Ep Es El Ez Ea Eml Epl Ems Ehw Hins Hbs.
  pose proof (mt_ms t Hm) as Hms. pose proof FR as [F1 F2 F3 F4 F5].
  assert (Hms' : RK.ms_inv t').
  { destruct Hms as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10].
    unfold MsDefs.ms_chain_ok in C1.
    constructor; unfold MsDefs.ms_chain_ok; rewrite ?F1, ?Eh, ?Ep, ?Es, ?El, ?Ez; try assumption.
    rewrite Es in Hins. exact Hins. }
  apply (mt_inv_trip t t' Hm Hms').
  - intros Hq. rewrite F1 in Hq. pose proof (mt_fast t Hm Hq) as HF.
    unfold MsDefs.ms_fast_inv in *. rewrite Eml, Epl. exact HF.
  - intros Hq. rewrite F1 in Hq. pose proof (mt_slow t Hm Hq) as HS.
    unfold MsDefs.ms_slow_inv in *. rewrite Eml, El, Es, Ems, F1. exact HS.
  - exact FR.
  - exact Ew.
  - exact Ehw.
  - destruct Ea as [Ea|Ea]; rewrite Ea; [rewrite Es; exact (mt_ma t Hm) | left; reflexivity].
  - rewrite Eml. exact (proj1 (mt_ml t Hm)).
  - rewrite Epl. exact (proj2 (mt_ml t Hm)).
  - rewrite Es, El. reflexivity.
  - rewrite Es. lia.
  - exact Hbs.
  - left. exact Ems.
  - rewrite Eml, Es. exact (mt_pend t Hm).
Qed.

Lemma mt_inv_set_insert : forall t v,
  mt_inv t -> 0 <= v <= RD.ls_strstart (RD.d_ls t) ->
  mt_inv (RD.setD_ls (RD.setL_insert v (RD.d_ls t)) t).
Proof.
  intros t v Hm Hv. apply (mt_inv_lsonly t _ Hm); try (constructor; reflexivity). exact Hv.
Qed.

Lemma mt_inv_flush_block : forall last t, mt_inv t -> mt_inv (snd (RD.flush_block last t)).
Proof.
  intros last t Hm. destruct (rt_fb_frame last t) as [FR FL].
  pose proof (RK.mi_ins _ (mt_ms t Hm)) as Hi.
  apply (mt_inv_lsonly t _ Hm); try (rewrite FL; reflexivity); try (left; rewrite FL; reflexivity).
  - exact FR.
  - rewrite FL. exact Hi.
  - right. rewrite FL. rt_ls. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The tail                                                              *)
(* ------------------------------------------------------------------------- *)

(** RT's [ds_tail] after its pending literal and its [insert] update. *)
Definition rt_tail_core (flush : Z) (s2 : RD.DSt) : RD.BlockState * RD.DSt :=
  if Z.eqb flush Base.Z_FINISH then
    match RD.flush_block 1 s2 with
    | (Some bs, s3) => (bs, s3)
    | (None, s3) => (RD.FinishDone, s3)
    end
  else if negb (Z.eqb (RT.ts_symnext (RD.d_ts s2)) 0) then
    match RD.flush_block 0 s2 with
    | (Some bs, s3) => (bs, s3)
    | (None, s3) => (RD.BlockDone, s3)
    end
  else (RD.BlockDone, s2).

Lemma rt_tail_fast_shape : forall flush t,
  RD.ds_tail flush false true t
  = rt_tail_core flush
      (RD.setD_ls (RD.setL_insert (if Z.ltb (RD.ls_strstart (RD.d_ls t)) (RC.MIN_MATCH - 1)
                                   then RD.ls_strstart (RD.d_ls t) else RC.MIN_MATCH - 1)
                                  (RD.d_ls t)) t).
Proof. intros flush t. reflexivity. Qed.

Lemma em_inv_of_sym0 : forall s, em_core s -> DS.ds_sym_next s = 0 -> em_inv s.
Proof.
  intros s He E. split; [exact He|]. pose proof (ec_sn s He) as A. pose proof (ec_lbs s He) as B. lia.
Qed.

(** From group D's [em_core] alone: the tail runs after a pending literal
    may have filled the symbol buffer. *)
Theorem m_tail_core : forall s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_core s ->
  bs_of (snd (SBlk.deflate_tail s flush)) = fst (rt_tail_core flush t)
  /\ dst_rel (fst (SBlk.deflate_tail s flush)) (snd (rt_tail_core flush t)) po pi
  /\ mt_inv (snd (rt_tail_core flush t))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (SBlk.deflate_tail s flush))) <> 0 ->
      em_inv (fst (SBlk.deflate_tail s flush))).
Proof.
  intros s t po pi flush Hd Hm He.
  pose proof Hd as (_ & _ & _ & (Hsn & _) & _).
  unfold SBlk.deflate_tail, rt_tail_core. unfold Z_FINISH, Base.Z_FINISH.
  destruct (Z.eqb flush 4).
  - destruct (pair_flush_block s t po pi 1 Hd He (m_fb_lz t Hm) ltac:(lia)) as (Y1 & Y2 & Y3).
    pose proof (mt_inv_flush_block 1 t Hm) as Hm'.
    destruct (SBlk.flush_block s 1) as [s' [b|]]; destruct (RD.flush_block 1 t) as [[b'|] t'];
      cbn [fst snd option_map] in Y1, Y2, Y3, Hm' |- *; try discriminate.
    + injection Y2 as Eb. split; [exact Eb|]. split; [exact Y1|]. split; [exact Hm' | exact Y3].
    + split; [reflexivity|]. split; [exact Y1|]. split; [exact Hm' | exact Y3].
  - rewrite Hsn. destruct (Z.eqb_spec (RT.ts_symnext (RD.d_ts t)) 0) as [E0|E0]; cbn [negb].
    2:{ destruct (pair_flush_block s t po pi 0 Hd He (m_fb_lz t Hm) ltac:(lia)) as (Y1 & Y2 & Y3).
      pose proof (mt_inv_flush_block 0 t Hm) as Hm'.
      destruct (SBlk.flush_block s 0) as [s' [b|]]; destruct (RD.flush_block 0 t) as [[b'|] t'];
        cbn [fst snd option_map] in Y1, Y2, Y3, Hm' |- *; try discriminate.
      * injection Y2 as Eb. split; [exact Eb|]. split; [exact Y1|]. split; [exact Hm' | exact Y3].
      * split; [reflexivity|]. split; [exact Y1|]. split; [exact Hm' | exact Y3]. }
    cbn [fst snd]. split; [reflexivity|]. split; [exact Hd|]. split; [exact Hm|]. intros _.
    apply em_inv_of_sym0; [exact He|]. rewrite Hsn. exact E0.
Qed.

(** S5's [set_insert] against RT's [setL_insert]. *)
Lemma m_tail_insert : forall s t po pi v5 v,
  dst_rel s t po pi -> mt_inv t -> em_inv s -> v5 = v -> 0 <= v <= RD.ls_strstart (RD.d_ls t) ->
  dst_rel (DS.set_insert s v5) (RD.setD_ls (RD.setL_insert v (RD.d_ls t)) t) po pi
  /\ mt_inv (RD.setD_ls (RD.setL_insert v (RD.d_ls t)) t) /\ em_inv (DS.set_insert s v5).
Proof.
  intros s t po pi v5 v Hd Hm He Hv Hr.
  pose proof Hd as (_ & Hl0 & _).
  assert (Hl : lz_rel s (RD.setD_ls (RD.d_ls t) t)) by (rewrite rt_setD_ls_eta; exact Hl0).
  split; [|split].
  - apply (m_lz_step s _ t _ po pi Hd); [reflexivity|]. exact (lz_set_insert s t (RD.d_ls t) v5 v Hl Hv).
  - exact (mt_inv_set_insert t v Hm Hr).
  - exact (em_inv_frame s (DS.set_insert s v5) (MFill2.m_em_of_nonlz s (DS.set_insert s v5) eq_refl) He).
Qed.

Theorem m_fast_tail : forall s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_inv s ->
  let s2 := DS.set_insert s (if Z.ltb (DS.ds_strstart s) (DS.MIN_MATCH - 1)
                             then DS.ds_strstart s else DS.MIN_MATCH - 1) in
  bs_of (snd (SBlk.deflate_tail s2 flush)) = fst (RD.ds_tail flush false true t)
  /\ dst_rel (fst (SBlk.deflate_tail s2 flush)) (snd (RD.ds_tail flush false true t)) po pi
  /\ mt_inv (snd (RD.ds_tail flush false true t))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (SBlk.deflate_tail s2 flush))) <> 0 ->
      em_inv (fst (SBlk.deflate_tail s2 flush))).
Proof.
  intros s t po pi flush Hd Hm He s2. subst s2. rewrite rt_tail_fast_shape.
  pose proof Hd as (_ & Hl & _).
  pose proof (RK.mi_str _ (mt_ms t Hm)) as Hst.
  assert (Hr : 0 <= (if Z.ltb (RD.ls_strstart (RD.d_ls t)) (RC.MIN_MATCH - 1)
                     then RD.ls_strstart (RD.d_ls t) else RC.MIN_MATCH - 1)
               <= RD.ls_strstart (RD.d_ls t)).
  { unfold RC.MIN_MATCH. destruct (Z.ltb_spec (RD.ls_strstart (RD.d_ls t)) (3 - 1)); lia. }
  assert (Hv : (if Z.ltb (DS.ds_strstart s) (DS.MIN_MATCH - 1) then DS.ds_strstart s else DS.MIN_MATCH - 1)
               = (if Z.ltb (RD.ls_strstart (RD.d_ls t)) (RC.MIN_MATCH - 1)
                  then RD.ls_strstart (RD.d_ls t) else RC.MIN_MATCH - 1))
    by (rewrite (lzr_ss _ _ Hl); reflexivity).
  destruct (m_tail_insert s t po pi _ _ Hd Hm He Hv Hr) as (J1 & J2 & J3).
  exact (m_tail_core _ _ po pi flush J1 J2 (em_inv_core _ J3)).
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  D14: deflate_fast                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem m_deflate_fast : forall s t pre_out pre_in flush,
  dst_rel s t pre_out pre_in -> mt_inv t -> em_inv s ->
  1 <= RC.dg_level (RD.d_cfg t) <= 3 ->
  bs_of (snd (SBlk.deflate_fast s flush)) = fst (RD.deflate_fast flush t)
  /\ dst_rel (fst (SBlk.deflate_fast s flush)) (snd (RD.deflate_fast flush t)) pre_out pre_in
  /\ mt_inv (snd (RD.deflate_fast flush t))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (SBlk.deflate_fast s flush))) <> 0 ->
      em_inv (fst (SBlk.deflate_fast s flush))).
Proof.
  intros s t po pi flush Hd Hm He Hlev.
  pose proof (msr_nonneg t Hm) as H0. unfold msr in H0.
  assert (Hn : msr t < Z.of_nat (SBlk.lz_fuel s)).
  { pose proof Hd as (_ & Hl & _). unfold SBlk.lz_fuel, msr.
    rewrite (MFill4.m_avail_zlen s t po pi Hd), (lzr_la _ _ Hl). lia. }
  assert (Hf : msr t < Z.of_nat (RD.ds_fuel t)) by (unfold RD.ds_fuel, msr; lia).
  pose proof (m_fast_loop _ _ s t po pi flush Hd Hm He Hlev Hn Hf) as HL.
  unfold SBlk.deflate_fast, RD.deflate_fast.
  destruct (SBlk.deflate_fast_loop (SBlk.lz_fuel s) s flush) as [s1 [b|]];
    destruct (RD.df_loop (RD.ds_fuel t) flush t) as [[b'|] t1]; cbn [floop_rel] in HL; try contradiction.
  - exact HL.
  - destruct HL as (H1 & H2 & H3). exact (m_fast_tail s1 t1 po pi flush H1 H2 H3).
Qed.
