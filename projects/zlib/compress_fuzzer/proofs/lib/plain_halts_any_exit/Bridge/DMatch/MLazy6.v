(** * Bridge.DMatch.MLazy6 — group M: pair D15, the whole [deflate_slow]
    ([m_deflate_slow]).

    The loop ([m_slow_loop]): S5's [deflate_slow_loop] against RT's
    [ds_loop], trip by trip through [MLazy5.m_slow_step]; the fuels are
    deflate_fast's and the same measure bounds them.  The tail
    ([m_slow_tail]): the pending literal, if any ([m_tail_lit]: S5 tallies
    it and drops the buffer-full flag, as RT does), then [set_insert] and
    [deflate_tail] against [ds_tail flush true true] ([MFast7.m_tail_core],
    which needs only group D's [em_core]: the literal may have filled the
    symbol buffer). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast2 MFast6
  MFast7 MLazy5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill2 MFill4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.
Module STr := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.

(* ------------------------------------------------------------------------- *)
(* 1.  The loop                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem m_slow_loop : forall n m s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_inv s -> 4 <= RC.dg_level (RD.d_cfg t) <= 9 ->
  msr t < Z.of_nat n -> msr t < Z.of_nat m ->
  floop_rel po pi (SBlk.deflate_slow_loop n s flush) (RD.ds_loop m flush t).
Proof.
  induction n as [|n IH]; intros m s t po pi flush Hd Hm He Hlev Hn Hmm;
    pose proof (msr_nonneg t Hm) as H0; [lia|].
  destruct m as [|m]; [lia|].
  pose proof (m_slow_step s t po pi flush Hd Hm He Hlev) as Hs.
  cbn [SBlk.deflate_slow_loop RD.ds_loop].
  destruct (SBlk.deflate_slow_body s flush) as [s' [| |bs]];
    destruct (RD.ds_step flush t) as [t'|bs' t'|t']; cbn [fstep_rel] in Hs; try contradiction.
  - destruct Hs as (H1 & H2 & H3 & H4 & H5).
    apply IH; try assumption; [rewrite H5; exact Hlev | lia | lia].
  - exact Hs.
  - exact Hs.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The tail                                                              *)
(* ------------------------------------------------------------------------- *)

Definition s5_tail_lit (s : DS.deflate_state) : DS.deflate_state :=
  if negb (Z.eqb (DS.ds_match_available s) 0) then
    let '(s, _) := STr.tr_tally_lit s (arr_get (DS.ds_window s) (DS.ds_strstart s - 1)) in
    DS.set_match_available s 0
  else s.

Definition rt_tail_lit (t : RD.DSt) : RD.DSt :=
  if negb (Z.eqb (RD.ls_matchavail (RD.d_ls t)) 0) then
    let tt := RT.tr_tally_lit (RD.ls_window (RD.d_ls t) (RD.ls_strstart (RD.d_ls t) - 1))
                              (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t) in
    RD.setD_ls (RD.setL_matchavail 0 (RD.d_ls t)) (RD.setD_ts (snd tt) t)
  else t.

Lemma rt_tail_slow_shape : forall flush t,
  RD.ds_tail flush true true t
  = rt_tail_core flush
      (RD.setD_ls (RD.setL_insert (if Z.ltb (RD.ls_strstart (RD.d_ls (rt_tail_lit t))) (RC.MIN_MATCH - 1)
                                   then RD.ls_strstart (RD.d_ls (rt_tail_lit t)) else RC.MIN_MATCH - 1)
                                  (RD.d_ls (rt_tail_lit t))) (rt_tail_lit t)).
Proof. intros flush t. reflexivity. Qed.

Theorem m_tail_lit : forall s t po pi,
  dst_rel s t po pi -> mt_inv t -> em_inv s ->
  dst_rel (s5_tail_lit s) (rt_tail_lit t) po pi /\ mt_inv (rt_tail_lit t) /\ em_core (s5_tail_lit s).
Proof.
  intros s t po pi Hd Hm He.
  pose proof Hd as (_ & Hl & _).
  pose proof (lzr_ma _ _ Hl) as Ema. pose proof (lzr_ss _ _ Hl) as Ess. pose proof (lzr_win _ _ Hl) as Hrw.
  pose proof (mt_ws t Hm) as Hws. rewrite Hws in Hrw.
  pose proof (mt_ma t Hm) as Hma0. pose proof (mt_ms t Hm) as Hms.
  pose proof (RK.mi_room _ Hms) as Hrm. pose proof (RK.mi_look _ Hms) as Hlk. rewrite Hws in Hrm.
  unfold s5_tail_lit, rt_tail_lit. rewrite Ema.
  destruct (Z.eqb_spec (RD.ls_matchavail (RD.d_ls t)) 0) as [E0|E0]; cbn [negb].
  - split; [exact Hd|]. split; [exact Hm | exact (em_inv_core s He)].
  - assert (Hss1 : 1 <= RD.ls_strstart (RD.d_ls t)) by (destruct Hma0 as [M|[M1 M2]]; [lia | exact M2]).
    assert (Ew : arr_get (DS.ds_window s) (DS.ds_strstart s - 1) = RD.ls_window (RD.d_ls t) (RD.ls_strstart (RD.d_ls t) - 1))
      by (rewrite Ess; apply Hrw; lia).
    cbv zeta. rewrite Ew.
    destruct (pair_tr_tally_lit s t po pi (RD.ls_window (RD.d_ls t) (RD.ls_strstart (RD.d_ls t) - 1)) Hd He)
      as (T1 & T2 & T3 & T4).
    destruct (STr.tr_tally_lit s (RD.ls_window (RD.d_ls t) (RD.ls_strstart (RD.d_ls t) - 1))) as [st bf] eqn:ET.
    cbn [fst snd] in T1, T2, T3, T4.
    set (t' := RD.setD_ts (snd (RT.tr_tally_lit (RD.ls_window (RD.d_ls t) (RD.ls_strstart (RD.d_ls t) - 1))
                                  (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))) t) in *.
    pose proof T1 as (_ & Hl1 & _).
    assert (Hl1' : lz_rel st (RD.setD_ls (RD.d_ls t') t')) by (rewrite rt_setD_ls_eta; exact Hl1).
    pose proof (lz_set_match_available st t' (RD.d_ls t') 0 0 Hl1' eq_refl) as A1.
    split; [|split].
    + eapply m_lz_step; [exact T1 | reflexivity | exact A1].
    + apply (mt_inv_lsonly t _ Hm); try (constructor; reflexivity).
      all: first [right; reflexivity | exact (RK.mi_ins _ Hms)].
    + exact (em_core_frame st _ (MFill2.m_em_of_nonlz st (DS.set_match_available st 0) eq_refl) T3).
Qed.

Lemma m_tail_insert_core : forall s t po pi v5 v,
  dst_rel s t po pi -> mt_inv t -> em_core s -> v5 = v -> 0 <= v <= RD.ls_strstart (RD.d_ls t) ->
  dst_rel (DS.set_insert s v5) (RD.setD_ls (RD.setL_insert v (RD.d_ls t)) t) po pi
  /\ mt_inv (RD.setD_ls (RD.setL_insert v (RD.d_ls t)) t) /\ em_core (DS.set_insert s v5).
Proof.
  intros s t po pi v5 v Hd Hm He Hv Hr.
  pose proof Hd as (_ & Hl0 & _).
  assert (Hl : lz_rel s (RD.setD_ls (RD.d_ls t) t)) by (rewrite rt_setD_ls_eta; exact Hl0).
  split; [|split].
  - apply (m_lz_step s _ t _ po pi Hd); [reflexivity|]. exact (lz_set_insert s t (RD.d_ls t) v5 v Hl Hv).
  - exact (mt_inv_set_insert t v Hm Hr).
  - exact (em_core_frame s (DS.set_insert s v5) (MFill2.m_em_of_nonlz s (DS.set_insert s v5) eq_refl) He).
Qed.

Theorem m_slow_tail : forall s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_inv s ->
  let s1 := s5_tail_lit s in
  let s2 := DS.set_insert s1 (if Z.ltb (DS.ds_strstart s1) (DS.MIN_MATCH - 1)
                              then DS.ds_strstart s1 else DS.MIN_MATCH - 1) in
  bs_of (snd (SBlk.deflate_tail s2 flush)) = fst (RD.ds_tail flush true true t)
  /\ dst_rel (fst (SBlk.deflate_tail s2 flush)) (snd (RD.ds_tail flush true true t)) po pi
  /\ mt_inv (snd (RD.ds_tail flush true true t))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (SBlk.deflate_tail s2 flush))) <> 0 ->
      em_inv (fst (SBlk.deflate_tail s2 flush))).
Proof.
  intros s t po pi flush Hd Hm He s1 s2. subst s2 s1. rewrite rt_tail_slow_shape.
  destruct (m_tail_lit s t po pi Hd Hm He) as (J1 & J2 & J3).
  pose proof J1 as (_ & Hl & _).
  pose proof (RK.mi_str _ (mt_ms _ J2)) as Hst.
  assert (Hr : 0 <= (if Z.ltb (RD.ls_strstart (RD.d_ls (rt_tail_lit t))) (RC.MIN_MATCH - 1)
                     then RD.ls_strstart (RD.d_ls (rt_tail_lit t)) else RC.MIN_MATCH - 1)
               <= RD.ls_strstart (RD.d_ls (rt_tail_lit t))).
  { unfold RC.MIN_MATCH. destruct (Z.ltb_spec (RD.ls_strstart (RD.d_ls (rt_tail_lit t))) (3 - 1)); lia. }
  assert (Hv : (if Z.ltb (DS.ds_strstart (s5_tail_lit s)) (DS.MIN_MATCH - 1)
                then DS.ds_strstart (s5_tail_lit s) else DS.MIN_MATCH - 1)
               = (if Z.ltb (RD.ls_strstart (RD.d_ls (rt_tail_lit t))) (RC.MIN_MATCH - 1)
                  then RD.ls_strstart (RD.d_ls (rt_tail_lit t)) else RC.MIN_MATCH - 1))
    by (rewrite (lzr_ss _ _ Hl); reflexivity).
  destruct (m_tail_insert_core _ _ po pi _ _ J1 J2 J3 Hv Hr) as (K1 & K2 & K3).
  exact (m_tail_core _ _ po pi flush K1 K2 K3).
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  D15: deflate_slow                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem m_deflate_slow : forall s t pre_out pre_in flush,
  dst_rel s t pre_out pre_in -> mt_inv t -> em_inv s ->
  4 <= RC.dg_level (RD.d_cfg t) <= 9 ->
  bs_of (snd (SBlk.deflate_slow s flush)) = fst (RD.deflate_slow flush t)
  /\ dst_rel (fst (SBlk.deflate_slow s flush)) (snd (RD.deflate_slow flush t)) pre_out pre_in
  /\ mt_inv (snd (RD.deflate_slow flush t))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (SBlk.deflate_slow s flush))) <> 0 ->
      em_inv (fst (SBlk.deflate_slow s flush))).
Proof.
  intros s t po pi flush Hd Hm He Hlev.
  pose proof (msr_nonneg t Hm) as H0. unfold msr in H0.
  assert (Hn : msr t < Z.of_nat (SBlk.lz_fuel s)).
  { pose proof Hd as (_ & Hl & _). unfold SBlk.lz_fuel, msr.
    rewrite (MFill4.m_avail_zlen s t po pi Hd), (lzr_la _ _ Hl). lia. }
  assert (Hf : msr t < Z.of_nat (RD.ds_fuel t)) by (unfold RD.ds_fuel, msr; lia).
  pose proof (m_slow_loop _ _ s t po pi flush Hd Hm He Hlev Hn Hf) as HL.
  unfold SBlk.deflate_slow, RD.deflate_slow.
  destruct (SBlk.deflate_slow_loop (SBlk.lz_fuel s) s flush) as [s1 [b|]];
    destruct (RD.ds_loop (RD.ds_fuel t) flush t) as [[b'|] t1]; cbn [floop_rel] in HL; try contradiction.
  - exact HL.
  - destruct HL as (H1 & H2 & H3). exact (m_slow_tail s1 t1 po pi flush H1 H2 H3).
Qed.
