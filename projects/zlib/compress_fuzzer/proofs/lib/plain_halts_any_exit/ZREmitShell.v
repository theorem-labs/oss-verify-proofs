(** * ZREmitShell — the (default, zlib) emitter shell.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G5, part 4.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    One [zr_deflate ZR_DEFAULT_LEVEL 15] call unrolled end to end:
    entry checks (G5Chain.A1), zlib header (A2), dispatch to
    [deflate_slow] (A3), the slow-path walk pack
    ([SwSlow.deflate_slow_finish]), and — conditionally on the G6 bound
    seam ([bs = FinishDone] with [4 <= avail_out] at the walk's exit) —
    the trailer (A4) and the [Some enc] equation with
    [enc = [120; 156] ++ body ++ adler bytes].

    The G6 seam is deliberately a PREMISE of the final conditional
    conjunct: availout-sufficiency (the emitted stream fits
    [zr_deflate_bound]) is lane g6-bound's face, consuming exactly the
    [EvChain]/[EvOk] pack this theorem exports.  The other two walk
    outcomes ([NeedMore]/[FinishStarted]) are exported with their
    [avail_out = 0] witness, which is what that face refutes. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwStep SwDrain
  SwInit SwSlow G5Chain ZRTreeState ZREvSnap.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac dsimp :=
  cbn [d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype
       setZ_in setZ_done setZ_out setZ_availout setZ_totalin setZ_totalout
       setZ_adler setZ_datatype
       fst snd].

Local Ltac tsimp :=
  cbn [ts_bw ts_symbuf ts_symnext ts_trees ts_maxcode set_bw
       bw_out bw_buf bw_valid].

(* ==========================================================================
   1.  List arithmetic helpers.
   ========================================================================== *)

Lemma zlen_app : forall (a b : list Z), zlen (a ++ b) = zlen a + zlen b.
Proof.
  intros a b. unfold zlen. rewrite length_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma zlen_firstn_exact : forall n (l : list Z),
  0 <= n <= zlen l -> zlen (firstn (Z.to_nat n) l) = n.
Proof.
  intros n l [H0 H1]. unfold zlen in *.
  rewrite length_firstn, Nat.min_l.
  - apply Z2Nat.id; exact H0.
  - lia.
Qed.

Lemma skipn_zlen_all : forall (l : list Z), skipn (Z.to_nat (zlen l)) l = [].
Proof.
  intro l. unfold zlen. rewrite Nat2Z.id. apply skipn_all.
Qed.

(* ==========================================================================
   2.  [flush_pending] / [flush_block_only] shapes: the output ledger step,
       the drain fact, and the byte-writer register.
   ========================================================================== *)

Lemma bw_flush_valid0 : forall b, bw_valid b = 0 -> bw_flush b = b.
Proof. intros b Hv. unfold bw_flush. rewrite Hv. reflexivity. Qed.

(** One flush: output grows by exactly the availout drop; availout stays
    nonnegative; a positive leftover availout means the pending queue is
    DRAINED; the register's bit count is [bw_flush]'s. *)
Lemma flush_pending_shape : forall s,
  0 <= zs_availout (d_strm s) ->
  exists mv,
    zs_out (d_strm (flush_pending s)) = zs_out (d_strm s) ++ mv
    /\ zlen mv = zs_availout (d_strm s)
                 - zs_availout (d_strm (flush_pending s))
    /\ 0 <= zs_availout (d_strm (flush_pending s))
    /\ (0 < zs_availout (d_strm (flush_pending s)) ->
        bw_out (ts_bw (d_ts (flush_pending s))) = [])
    /\ bw_valid (ts_bw (d_ts (flush_pending s)))
       = bw_valid (bw_flush (ts_bw (d_ts s))).
Proof.
  intros s Havo.
  unfold flush_pending. cbv zeta.
  set (ts := tr_flush_bits (d_ts s)).
  set (pd := bw_out (ts_bw ts)).
  set (len0 := zlen pd).
  set (len := if Z.ltb (zs_availout (d_strm s)) len0
              then zs_availout (d_strm s) else len0).
  assert (Hpdz : len0 = zlen pd) by reflexivity.
  pose proof (zlen_nonneg pd) as Hpd0.
  assert (Hcase : len = zs_availout (d_strm s)
                  \/ (len = len0 /\ len0 <= zs_availout (d_strm s))).
  { unfold len.
    destruct (Z.ltb (zs_availout (d_strm s)) len0) eqn:El.
    - left; reflexivity.
    - right. split; [reflexivity | apply Z.ltb_ge; exact El]. }
  assert (Hlen_lo : 0 <= len).
  { destruct Hcase as [-> | [-> _]]; lia. }
  assert (Hlen_hi : len <= len0).
  { unfold len.
    destruct (Z.ltb (zs_availout (d_strm s)) len0) eqn:El.
    - apply Z.ltb_lt in El. lia.
    - lia. }
  assert (Hlen_avo : len <= zs_availout (d_strm s)).
  { destruct Hcase as [-> | [-> Hle]]; lia. }
  destruct (Z.eqb len 0) eqn:Elen0.
  - (* nothing moved *)
    apply Z.eqb_eq in Elen0.
    exists []. dsimp.
    rewrite app_nil_r.
    split; [reflexivity|].
    split; [change (zlen (@nil Z)) with 0; lia|].
    split; [exact Havo|].
    split.
    + intro Hpos.
      assert (Hl00 : len0 = 0).
      { destruct Hcase as [Ea | [El _]]; lia. }
      apply zlen_nil. fold pd. lia.
    + reflexivity.
  - (* [len] bytes moved *)
    apply Z.eqb_neq in Elen0.
    dsimp.
    exists (firstn (Z.to_nat len) pd).
    assert (Hfl : zlen (firstn (Z.to_nat len) pd) = len)
      by (apply zlen_firstn_exact; lia).
    split; [reflexivity|].
    split; [rewrite Hfl; lia|].
    split; [lia|].
    split.
    + intro Hpos.
      assert (Hll : len = len0).
      { destruct Hcase as [Ea | [El _]]; lia. }
      rewrite Hll, Hpdz. apply skipn_zlen_all.
    + tsimp. reflexivity.
Qed.

(** The same ledger step for [flush_block_only]: the tree-flush prefix
    does not touch the stream's output/availout fields. *)
Lemma flush_block_only_shape : forall l s,
  0 <= zs_availout (d_strm s) ->
  exists mv,
    zs_out (d_strm (flush_block_only l s)) = zs_out (d_strm s) ++ mv
    /\ zlen mv = zs_availout (d_strm s)
                 - zs_availout (d_strm (flush_block_only l s))
    /\ 0 <= zs_availout (d_strm (flush_block_only l s))
    /\ (0 < zs_availout (d_strm (flush_block_only l s)) ->
        bw_out (ts_bw (d_ts (flush_block_only l s))) = []).
Proof.
  intros l s Havo.
  unfold flush_block_only. cbv zeta.
  match goal with
  | |- context [flush_pending ?X] => set (s2 := X)
  end.
  assert (E2o : zs_out (d_strm s2) = zs_out (d_strm s))
    by (unfold s2; dsimp; reflexivity).
  assert (E2a : zs_availout (d_strm s2) = zs_availout (d_strm s))
    by (unfold s2; dsimp; reflexivity).
  destruct (flush_pending_shape s2 ltac:(rewrite E2a; exact Havo))
    as (mv & Ho & Hl & Hn & Hd & _).
  exists mv.
  rewrite Ho, Hl, E2o, E2a.
  repeat (split; [reflexivity || assumption |]).
  exact Hd.
Qed.

(** The final block's flush windups the bit register: [tr_flush_block]
    at [last = 1] (positive level) ends bit-aligned, and the flush keeps
    it that way. *)
Lemma tr_flush_block_last_valid : forall buf sl lvl strat dt ts0,
  0 < lvl ->
  bw_valid (ts_bw (snd (tr_flush_block buf sl 1 lvl strat dt ts0))) = 0.
Proof.
  intros buf sl lvl strat dt ts0 Hl.
  unfold tr_flush_block.
  rewrite (proj2 (Z.ltb_lt 0 lvl) Hl).
  cbv zeta iota.
  change (Z.eqb 1 0) with false. cbv iota.
  cbn [snd]. tsimp.
  apply (proj2 (bw_windup_empty _)).
Qed.

Lemma flush_block_only_last_valid : forall s,
  0 < dg_level (d_cfg s) ->
  bw_valid (ts_bw (d_ts (flush_block_only 1 s))) = 0.
Proof.
  intros s Hl.
  unfold flush_block_only. cbv zeta.
  match goal with
  | |- context [flush_pending ?X] => set (s2 := X)
  end.
  assert (Hv2 : bw_valid (ts_bw (d_ts s2)) = 0).
  { unfold s2. dsimp. apply tr_flush_block_last_valid. exact Hl. }
  unfold flush_pending. cbv zeta.
  set (ts := tr_flush_bits (d_ts s2)).
  assert (Hvts : bw_valid (ts_bw ts) = 0).
  { unfold ts, tr_flush_bits. tsimp.
    rewrite (bw_flush_valid0 _ Hv2). exact Hv2. }
  destruct (Z.eqb _ 0).
  - dsimp. exact Hvts.
  - dsimp. tsimp. exact Hvts.
Qed.

(* ==========================================================================
   3.  [EvChain] projections: the final state IS the last event's flush,
       the output ledger telescopes, snapshots keep availout nonneg.
   ========================================================================== *)

Lemma evchain_snoc_last : forall evs0 evf bw out avo bw' out' avo',
  EvChain (evs0 ++ [evf]) bw out avo bw' out' avo' ->
  bw' = ts_bw (d_ts (flush_block_only (fe_last evf) (fe_s evf)))
  /\ out' = zs_out (d_strm (flush_block_only (fe_last evf) (fe_s evf)))
  /\ avo' = zs_availout (d_strm (flush_block_only (fe_last evf) (fe_s evf))).
Proof.
  induction evs0 as [|e evs0 IH]; intros evf bw out avo bw' out' avo' HC.
  - cbn [app EvChain] in HC.
    destruct HC as (_ & _ & _ & HC).
    cbn [EvChain] in HC.
    destruct HC as (Hb & Ho & Ha).
    auto.
  - cbn [app EvChain] in HC.
    destruct HC as (_ & _ & _ & HC).
    exact (IH _ _ _ _ _ _ _ HC).
Qed.

Lemma evchain_out_extends : forall evs bw out avo bw' out' avo',
  0 <= avo ->
  EvChain evs bw out avo bw' out' avo' ->
  exists d, out' = out ++ d
    /\ zlen d = avo - avo'
    /\ 0 <= avo'.
Proof.
  induction evs as [|e evs IH]; intros bw out avo bw' out' avo' Havo HC.
  - cbn [EvChain] in HC. destruct HC as (_ & -> & ->).
    exists []. rewrite app_nil_r.
    split; [reflexivity|].
    split; [change (zlen (@nil Z)) with 0; lia|].
    exact Havo.
  - cbn [EvChain] in HC.
    destruct HC as (Hb & Ho & Ha & HC).
    destruct (flush_block_only_shape (fe_last e) (fe_s e)
                ltac:(rewrite Ha; exact Havo))
      as (mv & Fo & Fl & Fn & _).
    destruct (IH _ _ _ _ _ _ Fn HC) as (d & Ho' & Hl' & Ha').
    exists (mv ++ d).
    split.
    + rewrite Ho', Fo, Ho, <- app_assoc. reflexivity.
    + split; [|exact Ha'].
      rewrite zlen_app. lia.
Qed.

Lemma evchain_snapshots_avo : forall evs bw out avo bw' out' avo',
  0 <= avo ->
  EvChain evs bw out avo bw' out' avo' ->
  Forall (fun e => 0 <= zs_availout (d_strm (fe_s e))) evs.
Proof.
  induction evs as [|e evs IH]; intros bw out avo bw' out' avo' Havo HC.
  - constructor.
  - cbn [EvChain] in HC.
    destruct HC as (Hb & Ho & Ha & HC).
    constructor.
    + rewrite Ha. exact Havo.
    + destruct (flush_block_only_shape (fe_last e) (fe_s e)
                  ltac:(rewrite Ha; exact Havo))
        as (mv & _ & _ & Fn & _).
      exact (IH _ _ _ _ _ _ Fn HC).
Qed.

(* ==========================================================================
   4.  The zlib header at the default config, pinned byte-for-byte.
   ========================================================================== *)

(** At level 6 / windowBits 15 / strategy 0 / [strstart = 0] the header
    word is 0x789C = 30876 and the state change is exactly this tower. *)
Lemma zlib_header_pinned : forall s,
  dg_level (d_cfg s) = 6 ->
  dg_w_bits (d_cfg s) = 15 ->
  dg_strategy (d_cfg s) = 0 ->
  ls_strstart (d_ls s) = 0 ->
  zlib_header s
  = setD_status BUSY_STATE
      (setD_strm (setZ_adler (adler32_z 0 true []) (d_strm s))
         (setD_ts (putShortMSB 30876 (d_ts s)) s)).
Proof.
  intros s Hlvl Hwb Hstrat Hss.
  unfold zlib_header. cbv zeta.
  rewrite Hlvl, Hwb, Hstrat, Hss.
  reflexivity.
Qed.

(** A two-byte pending queue on an aligned register drains completely
    when [avail_out >= 2], and nothing else moves. *)
Lemma flush_pending_two : forall s b0 b1,
  bw_out (ts_bw (d_ts s)) = [b0; b1] ->
  bw_valid (ts_bw (d_ts s)) = 0 ->
  2 <= zs_availout (d_strm s) ->
  zs_out (d_strm (flush_pending s)) = zs_out (d_strm s) ++ [b0; b1]
  /\ zs_availout (d_strm (flush_pending s)) = zs_availout (d_strm s) - 2
  /\ bw_out (ts_bw (d_ts (flush_pending s))) = []
  /\ bw_valid (ts_bw (d_ts (flush_pending s))) = 0
  /\ bw_buf (ts_bw (d_ts (flush_pending s))) = bw_buf (ts_bw (d_ts s))
  /\ d_status (flush_pending s) = d_status s
  /\ d_wrap (flush_pending s) = d_wrap s
  /\ d_cfg (flush_pending s) = d_cfg s
  /\ d_ls (flush_pending s) = d_ls s
  /\ zs_in (d_strm (flush_pending s)) = zs_in (d_strm s)
  /\ zs_done (d_strm (flush_pending s)) = zs_done (d_strm s)
  /\ zs_totalin (d_strm (flush_pending s)) = zs_totalin (d_strm s)
  /\ zs_adler (d_strm (flush_pending s)) = zs_adler (d_strm s)
  /\ ts_symbuf (d_ts (flush_pending s)) = ts_symbuf (d_ts s)
  /\ ts_symnext (d_ts (flush_pending s)) = ts_symnext (d_ts s)
  /\ ts_trees (d_ts (flush_pending s)) TK_L = ts_trees (d_ts s) TK_L
  /\ ts_trees (d_ts (flush_pending s)) TK_D = ts_trees (d_ts s) TK_D.
Proof.
  intros s b0 b1 Hbw Hbv Havo.
  assert (Hfbw : ts_bw (tr_flush_bits (d_ts s)) = ts_bw (d_ts s))
    by (unfold tr_flush_bits; tsimp; apply bw_flush_valid0; exact Hbv).
  unfold flush_pending. cbv zeta.
  rewrite Hfbw, Hbw.
  change (zlen [b0; b1]) with 2.
  rewrite (proj2 (Z.ltb_ge (zs_availout (d_strm s)) 2) Havo).
  change (Z.eqb 2 0) with false. cbv iota.
  change (Z.to_nat 2) with 2%nat.
  cbn [firstn skipn].
  dsimp. tsimp.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hbv|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [unfold tr_flush_bits; tsimp; reflexivity|].
  split; [unfold tr_flush_bits; tsimp; reflexivity|].
  split; [unfold tr_flush_bits; tsimp; reflexivity|].
  unfold tr_flush_bits; tsimp; reflexivity.
Qed.

(* ==========================================================================
   5.  The default config, by value.
   ========================================================================== *)

Lemma zr_g15_facts : exists g,
  defl_init2 (-1) 8 15 8 0 = Some g
  /\ dg_level g = 6
  /\ dg_strategy g = 0
  /\ dg_wrap g = 1
  /\ dg_w_bits g = 15
  /\ GeomOk2 g 15 15.
Proof.
  destruct (defl_init2 (-1) 8 15 8 0) as [g|] eqn:Eg.
  - exists g.
    assert (Eg' := Eg). vm_compute in Eg'.
    injection Eg' as Eg''. subst g.
    split; [exact Eg|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    pose proof swtally_geom2_zr as G.
    vm_compute in G.
    exact (proj1 G).
  - vm_compute in Eg. discriminate Eg.
Qed.

(* ==========================================================================
   6.  The shell: one [zr_deflate ZR_DEFAULT_LEVEL 15] call, unrolled to
       the walk pack, with the trailer under the G6 seam.
   ========================================================================== *)

Theorem emitter_shell : forall x,
  Forall (fun b => 0 <= b < 256) x ->
  exists g sd bs s' evs,
    defl_init2 (-1) 8 15 8 0 = Some g
    /\ dg_level g = 6
    /\ dg_strategy g = 0
    /\ dg_w_bits g = 15
    /\ GeomOk2 g 15 15
    /\ deflate_slow Z_FINISH sd = (bs, s')
    /\ d_cfg sd = g
    /\ d_wrap sd = 1
    /\ zs_out (d_strm sd) = [120; 156]
    /\ zs_availout (d_strm sd) = zr_deflate_bound 15 (zlen x) - 2
    /\ zs_in (d_strm sd) = x
    /\ zs_done (d_strm sd) = []
    /\ bw_out (ts_bw (d_ts sd)) = []
    /\ bw_valid (ts_bw (d_ts sd)) = 0
    /\ bw_buf (ts_bw (d_ts sd)) = 0
    /\ DsInv g 1 0 (fun _ => False) [] sd
    /\ Forall (EvOk g 1 (zs_done (d_strm s'))) evs
    /\ EvChain evs (ts_bw (d_ts sd)) (zs_out (d_strm sd))
                   (zs_availout (d_strm sd))
                   (ts_bw (d_ts s')) (zs_out (d_strm s'))
                   (zs_availout (d_strm s'))
    /\ zs_done (d_strm s') ++ zs_in (d_strm s') = x
    /\ d_wrap s' = 1
    /\ d_cfg s' = g
    /\ ( (exists evs0 evf,
            evs = evs0 ++ [evf]
            /\ Forall (fun e => fe_last e = 0) evs0
            /\ fe_last evf = 1
            /\ EvTile evs 0 (zlen (zs_done (d_strm s')))
            /\ zs_in (d_strm s') = []
            /\ zs_done (d_strm s') = x
            /\ CkInv 1 (d_strm s')
            /\ zs_totalin (d_strm s') = zlen x
            /\ ( (bs = FinishStarted /\ zs_availout (d_strm s') = 0)
               \/ (bs = FinishDone /\ 0 <= zs_availout (d_strm s')) ))
       \/ (bs = NeedMore /\ zs_availout (d_strm s') = 0
           /\ Forall (fun e => fe_last e = 0) evs) )
    /\ (bs = FinishDone -> 4 <= zs_availout (d_strm s') ->
        exists body,
          zs_out (d_strm s') = [120; 156] ++ body
          /\ zlen body = (zr_deflate_bound 15 (zlen x) - 2)
                         - zs_availout (d_strm s')
          /\ zr_deflate ZR_DEFAULT_LEVEL 15 x
             = Some ([120; 156] ++ body
                 ++ [u8 (Z.shiftr (Z.shiftr (zs_adler (d_strm s')) 16) 8);
                     u8 (Z.land (Z.shiftr (zs_adler (d_strm s')) 16) 255);
                     u8 (Z.shiftr (Z.land (zs_adler (d_strm s')) 65535) 8);
                     u8 (Z.land (Z.land (zs_adler (d_strm s')) 65535) 255)]))
    /\ (exists te, EvTile evs 0 te /\ te <= zlen (zs_done (d_strm s')))
    /\ ZRTreeInv (d_ts sd)
    /\ ZRTreeInv (d_ts s')
    /\ Forall (EvSnapOk g) evs
    /\ dg_max_dist g = 32506.
Proof.
  intros x Hx.
  destruct zr_g15_facts as (g & Eg & Hlvl & Hstrat & Hwrapg & Hwb & Hgeom).
  set (s1 := setD_strm
               (setZ_availout (zr_deflate_bound 15 (zlen x))
                  (setZ_in x (d_strm (deflate_reset g 1))))
               (deflate_reset g 1)).
  assert (HB : 13 <= zr_deflate_bound 15 (zlen x)).
  { unfold zr_deflate_bound.
    change (zr_wraplen 15) with 6.
    pose proof (zlen_nonneg x) as Hz0.
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 12) Hz0).
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 14) Hz0).
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 25) Hz0).
    lia. }
  assert (Hst1 : d_status s1 = INIT_STATE) by reflexivity.
  assert (Hwr1 : d_wrap s1 = 1) by reflexivity.
  assert (Hcfg1 : d_cfg s1 = g) by reflexivity.
  assert (Havo1 : zs_availout (d_strm s1) = zr_deflate_bound 15 (zlen x))
    by reflexivity.
  assert (Hin1 : zs_in (d_strm s1) = x) by reflexivity.
  assert (Hbw1 : bw_out (ts_bw (d_ts s1)) = []) by (vm_compute; reflexivity).
  assert (Hbv1 : bw_valid (ts_bw (d_ts s1)) = 0) by (vm_compute; reflexivity).
  assert (Hss1 : ls_strstart (d_ls s1) = 0) by (vm_compute; reflexivity).
  assert (Hbs1 : ls_blockstart (d_ls s1) = 0) by (vm_compute; reflexivity).
  (* A1: entry *)
  set (hs := setD_lastflush Z_FINISH s1).
  assert (E1 : deflate Z_FINISH s1 = deflate_body Z_FINISH hs).
  { apply deflate_entry.
    - rewrite Hst1. unfold INIT_STATE, FINISH_STATE. lia.
    - rewrite Havo1. lia.
    - exact Hbw1. }
  (* A2: the header *)
  assert (E2 : deflate_body Z_FINISH hs
               = deflate_run Z_FINISH (flush_pending (zlib_header hs))).
  { apply deflate_body_header.
    - exact Hst1.
    - exact Hwr1.
    - exact Hbw1.
    - exact Hbv1.
    - exact Hss1.
    - change (zs_availout (d_strm hs)) with (zs_availout (d_strm s1)).
      rewrite Havo1. lia. }
  assert (Hpin : zlib_header hs
    = setD_status BUSY_STATE
        (setD_strm (setZ_adler (adler32_z 0 true []) (d_strm hs))
           (setD_ts (putShortMSB 30876 (d_ts hs)) hs))).
  { apply zlib_header_pinned.
    - change (d_cfg hs) with (d_cfg s1). rewrite Hcfg1. exact Hlvl.
    - change (d_cfg hs) with (d_cfg s1). rewrite Hcfg1. exact Hwb.
    - change (d_cfg hs) with (d_cfg s1). rewrite Hcfg1. exact Hstrat.
    - exact Hss1. }
  set (zh := setD_status BUSY_STATE
               (setD_strm (setZ_adler (adler32_z 0 true []) (d_strm hs))
                  (setD_ts (putShortMSB 30876 (d_ts hs)) hs))).
  assert (Hbwzh : bw_out (ts_bw (d_ts zh)) = [120; 156])
    by (vm_compute; reflexivity).
  assert (Hbvzh : bw_valid (ts_bw (d_ts zh)) = 0)
    by (vm_compute; reflexivity).
  assert (Havozh : 2 <= zs_availout (d_strm zh)).
  { unfold zh. dsimp.
    change (zs_availout (d_strm hs)) with (zs_availout (d_strm s1)).
    rewrite Havo1. lia. }
  destruct (flush_pending_two zh 120 156 Hbwzh Hbvzh Havozh)
    as (Fout & Favo & Fbw & Fbv & Fbuf & Fstat & Fwrap & Fcfg & Fls & Fin
        & Fdn & Fti & Fad & Fsb & Fsn & FtL & FtD).
  set (sd := flush_pending zh) in *.
  assert (Houtsd : zs_out (d_strm sd) = [120; 156])
    by (rewrite Fout; vm_compute; reflexivity).
  assert (Havosd : zs_availout (d_strm sd) = zr_deflate_bound 15 (zlen x) - 2)
    by (rewrite Favo; vm_compute; reflexivity).
  assert (Hinsd : zs_in (d_strm sd) = x)
    by (rewrite Fin; vm_compute; reflexivity).
  assert (Hdnsd : zs_done (d_strm sd) = [])
    by (rewrite Fdn; vm_compute; reflexivity).
  assert (Hcfgsd : d_cfg sd = g)
    by (rewrite Fcfg; vm_compute; reflexivity).
  assert (Hwrapsd : d_wrap sd = 1)
    by (rewrite Fwrap; vm_compute; reflexivity).
  assert (Hstatsd : d_status sd = BUSY_STATE)
    by (rewrite Fstat; vm_compute; reflexivity).
  assert (Hlssd : d_ls sd = d_ls (deflate_reset g 1))
    by (rewrite Fls; vm_compute; reflexivity).
  assert (Hbs0 : ls_blockstart (d_ls sd) = 0)
    by (rewrite Hlssd; vm_compute; reflexivity).
  assert (Hbufsd : bw_buf (ts_bw (d_ts sd)) = 0)
    by (rewrite Fbuf; vm_compute; reflexivity).
  (* DsInv at the dispatch state *)
  assert (HI : DsInv g 1 0 (fun _ => False) [] sd).
  { apply (dsinv_init g 15 15 1 x sd Hgeom).
    - exact Hcfgsd.
    - exact Hwrapsd.
    - exact Hlssd.
    - rewrite Fsb. vm_compute. reflexivity.
    - rewrite Fsn. vm_compute. reflexivity.
    - rewrite FtL. vm_compute. reflexivity.
    - rewrite FtD. vm_compute. reflexivity.
    - exact Hinsd.
    - exact Hdnsd.
    - rewrite Fti. vm_compute. reflexivity.
    - split.
      + intros _. rewrite Fad, Hdnsd. vm_compute. reflexivity.
      + intros K. discriminate K.
    - exact Hx. }
  assert (Hmd : dg_max_dist g = 32506).
  { pose proof Eg as Eg2. vm_compute in Eg2.
    injection Eg2 as EgE. rewrite <- EgE. vm_compute. reflexivity. }
  (* the walk *)
  assert (Havosd0 : 0 <= zs_availout (d_strm sd)) by (rewrite Havosd; lia).
  destruct (deflate_slow_finish g 15 15 1 0 (fun _ => False) [] sd
              Hgeom Hstrat HI Havosd0)
    as (bs & s' & evs & Eslow & HFor & HCh & Hcons & Hdnx & Hout & FwS & FcS
        & Htile2 & HTIsw).
  (* dispatch plumbing *)
  assert (Edisp : dispatch Z_FINISH sd = (bs, s')).
  { rewrite (dispatch_slow sd).
    - exact Eslow.
    - rewrite Hcfgsd, Hlvl. lia.
    - rewrite Hcfgsd, Hlvl. lia.
    - rewrite Hcfgsd. exact Hstrat. }
  pose proof (deflate_run_arm sd bs s' Hstatsd Edisp) as Earm.
  (* the tree-state invariant, from the reset state through the header *)
  assert (HTIhs : ZRTreeInv (d_ts hs)) by (exact treeinv_init).
  assert (HTIzh : ZRTreeInv (d_ts zh)).
  { unfold zh. dsimp. unfold putShortMSB.
    apply treeinv_setbw. exact HTIhs. }
  assert (HTIsd : ZRTreeInv (d_ts sd))
    by (apply treeinv_flush_pending; exact HTIzh).
  assert (Hstatsd2 : ts_optlen (d_ts sd) = 0 /\ ts_statlen (d_ts sd) = 0).
  { apply statzero_flush_pending; unfold zh; dsimp;
    unfold putShortMSB, put_byte; apply statzero_setbw; exact statzero_init. }
  assert (Emlsd : ls_matchlen (d_ls sd) = MIN_MATCH - 1)
    by (rewrite Hlssd; vm_compute; reflexivity).
  assert (HSideSd : ZRSideInv g [] sd).
  { refine (conj HTIsd (conj (proj1 Hstatsd2) (conj (proj2 Hstatsd2)
              (conj (Forall_nil _) (conj _ _))))).
    - unfold FarPend. rewrite Emlsd.
      intros Habs. exfalso. unfold MIN_MATCH in Habs. lia.
    - unfold SldInv. rewrite Hbs0.
      intros Habs. exfalso. lia. }
  destruct (HTIsw ltac:(rewrite Hlvl; lia) HSideSd) as (HTIs' & HTIevs).
  (* assemble *)
  exists g, sd, bs, s', evs.
  split; [exact Eg|].
  split; [exact Hlvl|].
  split; [exact Hstrat|].
  split; [exact Hwb|].
  split; [exact Hgeom|].
  split; [exact Eslow|].
  split; [exact Hcfgsd|].
  split; [exact Hwrapsd|].
  split; [exact Houtsd|].
  split; [exact Havosd|].
  split; [exact Hinsd|].
  split; [exact Hdnsd|].
  split; [exact Fbw|].
  split; [exact Fbv|].
  split; [exact Hbufsd|].
  split; [exact HI|].
  split; [exact HFor|].
  split; [exact HCh|].
  split; [rewrite Hcons, Hdnsd, Hinsd; reflexivity|].
  split; [rewrite FwS; exact Hwrapsd|].
  split; [rewrite FcS; exact Hcfgsd|].
  split.
  { destruct Hout as [HL | HR].
    - left.
      destruct HL as (evs0 & evf & Ee & Hz0 & Hl1 & Htile & Ein' & Edone'
                      & HK & Hti' & Hbs2).
      exists evs0, evf.
      split; [exact Ee|].
      split; [exact Hz0|].
      split; [exact Hl1|].
      split.
      { replace (0 + ls_blockstart (d_ls sd)) with 0 in Htile
          by (rewrite Hbs0; lia).
        exact Htile. }
      split; [exact Ein'|].
      assert (Edx : zs_done (d_strm s') = x)
        by (rewrite Edone', Hdnsd, Hinsd; reflexivity).
      split; [exact Edx|].
      split; [exact HK|].
      split; [rewrite Hti', Edx; reflexivity|].
      exact Hbs2.
    - right. exact HR. }
  split.
  2:{ split.
      { destruct Htile2 as (te & Ht2 & Hle2).
        replace (0 + ls_blockstart (d_ls sd)) with 0 in Ht2
          by (rewrite Hbs0; lia).
        exists te. split; [exact Ht2 | exact Hle2]. }
      split; [exact HTIsd|]. split; [exact HTIs'|].
      split; [exact HTIevs | exact Hmd]. }
  (* the FinishDone conditional: trailer + the Some equation *)
  intros Hfd Havo4.
  destruct Hout as [HL | HR].
  2: { destruct HR as (Ebs & _ & _). rewrite Hfd in Ebs. discriminate Ebs. }
  destruct HL as (evs0 & evf & Ee & Hz0 & Hl1 & Htile & Ein' & Edone'
                  & HK & Hti' & Hbs2).
  rewrite Ee in HCh, HFor.
  destruct (evchain_snoc_last _ _ _ _ _ _ _ _ HCh) as (Ebw' & Eout2 & Eavo2).
  rewrite Hl1 in Ebw', Eout2, Eavo2.
  assert (Hsnap0 : 0 <= zs_availout (d_strm (fe_s evf))).
  { pose proof (evchain_snapshots_avo _ _ _ _ _ _ _ Havosd0 HCh) as HFa.
    apply Forall_app in HFa. destruct HFa as [_ HFa].
    apply Forall_inv in HFa. exact HFa. }
  assert (Hbw' : bw_out (ts_bw (d_ts s')) = []).
  { rewrite Ebw'.
    destruct (flush_block_only_shape 1 (fe_s evf) Hsnap0)
      as (mv & _ & _ & _ & Hd).
    apply Hd.
    rewrite <- Eavo2. lia. }
  assert (Hlvlf : 0 < dg_level (d_cfg (fe_s evf))).
  { apply Forall_app in HFor. destruct HFor as [_ HF1].
    apply Forall_inv in HF1.
    destruct HF1 as (Hcf & _).
    rewrite Hcf, Hlvl. lia. }
  assert (Hbv' : bw_valid (ts_bw (d_ts s')) = 0).
  { rewrite Ebw'. apply flush_block_only_last_valid. exact Hlvlf. }
  (* the trailer *)
  set (st := setD_status FINISH_STATE s').
  assert (Hwst : d_wrap st = 1).
  { change (d_wrap st) with (d_wrap s'). rewrite FwS. exact Hwrapsd. }
  assert (Hbwst : bw_out (ts_bw (d_ts st)) = [])
    by (change (d_ts st) with (d_ts s'); exact Hbw').
  assert (Hbvst : bw_valid (ts_bw (d_ts st)) = 0)
    by (change (d_ts st) with (d_ts s'); exact Hbv').
  assert (Havost : 4 <= zs_availout (d_strm st))
    by (change (d_strm st) with (d_strm s'); exact Havo4).
  pose proof (deflate_trailer_zlib st Hwst Hbwst Hbvst Havost) as HT.
  cbv zeta in HT.
  destruct HT as (Etr & Hto & Hwm1 & Hinp & Hdnp & Hadp & Htip).
  (* run -> trailer *)
  rewrite Hfd in Earm. cbv iota in Earm.
  assert (Ewleb : Z.leb (d_wrap (setD_status FINISH_STATE s')) 0 = false).
  { change (d_wrap (setD_status FINISH_STATE s')) with (d_wrap s').
    rewrite FwS, Hwrapsd. reflexivity. }
  rewrite Ewleb in Earm. cbv iota in Earm.
  fold st in Earm.
  (* the body via the output ledger *)
  destruct (evchain_out_extends _ _ _ _ _ _ _ Havosd0 HCh)
    as (body & Ebody & Elenb & _).
  exists body.
  assert (Eout' : zs_out (d_strm s') = [120; 156] ++ body)
    by (rewrite Ebody, Houtsd; reflexivity).
  split; [exact Eout'|].
  split; [rewrite Elenb, Havosd; reflexivity|].
  (* the Some equation *)
  unfold zr_deflate, ZR_DEFAULT_LEVEL, ZR_STRATEGY, defl_new.
  rewrite Eg. cbv iota.
  rewrite Hwrapg. cbv zeta.
  fold s1.
  rewrite E1, E2, Hpin.
  fold zh. fold sd.
  rewrite Earm, Etr.
  cbv iota.
  change (Z.eqb Z_STREAM_END Z_STREAM_END) with true.
  cbv iota.
  f_equal.
  rewrite Hto.
  change (zs_out (d_strm st)) with (zs_out (d_strm s')).
  rewrite Eout'.
  rewrite <- app_assoc.
  change (zs_adler (d_strm st)) with (zs_adler (d_strm s')).
  reflexivity.
Qed.

Print Assumptions emitter_shell.
