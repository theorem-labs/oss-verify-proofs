(** * ZHOEmit — l1_raw exact-fit characterization.

    OWNER: huffman-opt worker.  ADDITIVE ONLY: new names; ZRepro.v's
    zr_deflate and the face definitions are untouched.

      zr_deflate_room  — the same one-call shape with avail_out
                         = bound + extra (the counterfactual runner).
      zr_deflate_out   — the bytes written by the call, regardless of rc.
      zr_l1_raw_none_exact (LEMMA 2) — None happens ONLY at exact fit:
                         the written output length equals the bound.

    Falsifier verdicts (R68, before this file was written): the
    dichotomy holds both directions on the 16384k-1 family, two
    independent instruments (huffman-opt sweep k=20..100 + controls;
    l1-adversary corpus k=13..61); receipts in
    NUMBERS{,-ADDENDUM}.md.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre
  SwDrain SwInit SwStep SwLoop SwTail SwSlow G5Chain ZRTreeState ZREvSnap
  ZRThread ZREmitBody ZREmitBytes ZReproG6O ZReproG6A ZReproG6I ZReproG6J
  ZReproG6K ZReproG6L ZReproG6N ZReproG6P ZReproG6Q ZReproG6RawLen
  ZRRawShell DfArm DfIns DfArm1 DfArm2 DfStep DfLoop DfFast Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRL1FastNone
  ZRL1Close.
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

(* ==========================================================================
   1.  The additive runners.
   ========================================================================== *)

(** [zr_deflate]'s call shape with [extra] more bytes of room. *)
Definition zr_deflate_room (extra level windowBits : Z) (x : list Z)
  : option (list Z) :=
  match defl_new level 8 windowBits 8 ZR_STRATEGY with
  | None => None
  | Some s0 =>
      let s1 := setD_strm
                  (setZ_availout
                     (zr_deflate_bound windowBits (zlen x) + extra)
                     (setZ_in x (d_strm s0))) s0 in
      match deflate Z_FINISH s1 with
      | DfUnmodelled => None
      | DfRet code s2 =>
          if Z.eqb code Z_STREAM_END then Some (zs_out (d_strm s2))
          else None
      end
  end.

(** The bytes [zr_deflate]'s call writes, regardless of the return code. *)
Definition zr_deflate_out (level windowBits : Z) (x : list Z) : list Z :=
  match defl_new level 8 windowBits 8 ZR_STRATEGY with
  | None => []
  | Some s0 =>
      let s1 := setD_strm
                  (setZ_availout (zr_deflate_bound windowBits (zlen x))
                     (setZ_in x (d_strm s0))) s0 in
      match deflate Z_FINISH s1 with
      | DfUnmodelled => []
      | DfRet code s2 => zs_out (d_strm s2)
      end
  end.

(* ==========================================================================
   2.  availout conservation along a chain, as an EQUALITY (RawLen's
       [evchain_avail] states the <= half; the per-event fact is already
       an equality via [fbo_avail]).
   ========================================================================== *)

Lemma zho_evchain_avail_eq : forall evs bw out avo bw' out' avo',
  EvChain evs bw out avo bw' out' avo' ->
  0 <= avo ->
  0 <= avo' /\ zlen out' + avo' = zlen out + avo.
Proof.
  induction evs as [|ev r IH]; intros bw out avo bw' out' avo' HCh Ha;
    cbn [EvChain] in HCh.
  - destruct HCh as (Eb & Eo & Ea). subst.
    split; [exact Ha | reflexivity].
  - destruct HCh as (Hbw & Hout & Havo & HCh').
    destruct (fbo_avail (fe_last ev) (fe_s ev)
                ltac:(rewrite Havo; exact Ha)) as (E1 & E2 & E3).
    destruct (IH _ _ _ _ _ _ HCh' E2) as (I1 & I2).
    rewrite Hout, Havo in E1.
    split; [exact I1|].
    rewrite I2, E1. ring.
Qed.

(* ==========================================================================
   3.  LEMMA 2: [None] occurs ONLY at exact fit.
   ========================================================================== *)

Theorem zr_l1_raw_none_exact : forall x,
  ZR_Input x ->
  zr_deflate 1 (-15) x = None ->
  zlen (zr_deflate_out 1 (-15) x) = zr_deflate_bound (-15) (zlen x).
Proof.
  intros x HIn Hnone.
  destruct HIn as (Hx & Hcap).
  destruct zr_g1m15_facts
    as (g & Eg & Hlvl & Hstrat & Hwrapg & Hse & _ & _ & _ & _ & Hgeom).
  unfold zr_deflate, ZR_STRATEGY, defl_new in Hnone.
  unfold zr_deflate_out, ZR_STRATEGY, defl_new.
  rewrite Eg in Hnone |- *.
  cbv iota in Hnone |- *.
  rewrite Hwrapg in Hnone |- *.
  cbv zeta in Hnone |- *.
  set (s1 := setD_strm
               (setZ_availout (zr_deflate_bound (-15) (zlen x))
                  (setZ_in x (d_strm (deflate_reset g 0))))
               (deflate_reset g 0)) in *.
  pose proof (SwDrain.zlen_nonneg x) as Hxn.
  pose proof (zr_bound_lo_raw (zlen x) Hxn) as HB.
  (* the entry *)
  assert (Hst1 : d_status s1 = INIT_STATE) by (vm_compute; reflexivity).
  assert (Havo1 : zs_availout (d_strm s1)
                  = zr_deflate_bound (-15) (zlen x))
    by (unfold s1; dsimp; reflexivity).
  assert (Hbw1 : bw_out (ts_bw (d_ts s1)) = [])
    by (vm_compute; reflexivity).
  rewrite (deflate_entry s1
             ltac:(rewrite Hst1; intro K; discriminate K)
             ltac:(rewrite Havo1; lia)
             Hbw1) in Hnone |- *.
  (* the raw header phase: nothing, straight to BUSY *)
  rewrite (deflate_body_raw (setD_lastflush Z_FINISH s1)
             ltac:(dsimp; exact Hst1)
             ltac:(dsimp; unfold s1; dsimp; vm_compute; reflexivity))
    in Hnone |- *.
  set (sd := setD_status BUSY_STATE (setD_lastflush Z_FINISH s1)) in *.
  (* facts at the dispatch state *)
  assert (Hcfgsd : d_cfg sd = g) by (vm_compute; reflexivity).
  assert (Hwrapsd : d_wrap sd = 0) by (vm_compute; reflexivity).
  assert (Hstatsd : d_status sd = BUSY_STATE) by (vm_compute; reflexivity).
  assert (Hlssd : d_ls sd = d_ls (deflate_reset g 0))
    by (vm_compute; reflexivity).
  assert (Houtsd : zs_out (d_strm sd) = [])
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Havosd : zs_availout (d_strm sd)
                   = zr_deflate_bound (-15) (zlen x))
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Hinsd : zs_in (d_strm sd) = x)
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Hdnsd : zs_done (d_strm sd) = [])
    by (unfold sd, s1; dsimp; reflexivity).
  (* DsInv + DfSide at the dispatch state *)
  assert (HI : DsInv g 0 0 (fun _ => False) [] sd).
  { apply (dsinv_init g 15 15 0 x sd Hgeom).
    - exact Hcfgsd.
    - exact Hwrapsd.
    - exact Hlssd.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - exact Hinsd.
    - exact Hdnsd.
    - unfold sd, s1; dsimp; reflexivity.
    - split; intros K; discriminate K.
    - exact Hx. }
  assert (HSide : DfSide (d_ls sd)).
  { refine (conj _ (conj _ _)).
    - rewrite Hlssd. vm_compute. reflexivity.
    - rewrite Hlssd. vm_compute. reflexivity.
    - right. rewrite Hlssd. vm_compute. reflexivity. }
  (* the walk *)
  assert (Havosd0 : 0 <= zs_availout (d_strm sd)) by (rewrite Havosd; lia).
  assert (Hbs0sd : ls_blockstart (d_ls sd) = 0)
    by (rewrite Hlssd; vm_compute; reflexivity).
  assert (HBsFsd : BsFloor g sd).
  { unfold BsFloor. rewrite Hbs0sd. intro K. lia. }
  destruct (deflate_fast_finish g 15 15 0 0 (fun _ => False) [] sd
              Hgeom HI HBsFsd HSide Havosd0)
    as (bs & s' & evs & Efast & HFor & HCh & Hcons & Hdnx & Hout & FwS
        & FcS & Htile2 & HSnapw & _ & _).
  assert (Edisp : dispatch Z_FINISH sd = (bs, s')).
  { rewrite (dispatch_fast sd).
    - exact Efast.
    - rewrite Hcfgsd, Hlvl. lia.
    - rewrite Hcfgsd. exact Hstrat. }
  rewrite (deflate_run_arm sd bs s' Hstatsd Edisp) in Hnone |- *.
  (* conservation: written bytes + leftover room = the bound *)
  destruct (zho_evchain_avail_eq evs _ _ _ _ _ _ HCh Havosd0)
    as (Hav0' & Hsum).
  rewrite Houtsd, Havosd in Hsum.
  change (zlen []) with 0 in Hsum.
  (* the outcome arms *)
  destruct Hout as [HL | HR].
  2:{ (* NeedMore: avail_out exhausted mid-stream *)
      destruct HR as (Ebs & Eav0 & _).
      rewrite Ebs in Hnone |- *.
      cbv iota in Hnone |- *.
      rewrite Eav0 in Hnone |- *.
      change (Z.eqb 0 0) with true in Hnone |- *.
      cbv iota in Hnone |- *.
      dsimp.
      lia. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & Htile & Ein' & Edone'
                  & HK & Hti' & Hbs2).
  destruct Hbs2 as [(Ebs & Eav0)|(Ebs & Hav1)].
  - (* FinishStarted: exhausted at the final flush *)
    rewrite Ebs in Hnone |- *.
    cbv iota in Hnone |- *.
    change (zs_availout (d_strm (setD_status FINISH_STATE s')))
      with (zs_availout (d_strm s')) in Hnone |- *.
    rewrite Eav0 in Hnone |- *.
    change (Z.eqb 0 0) with true in Hnone |- *.
    cbv iota in Hnone |- *.
    dsimp.
    lia.
  - (* FinishDone: the call returns Some — contradicts None *)
    exfalso.
    rewrite Ebs in Hnone.
    cbv iota in Hnone.
    assert (Ewleb : Z.leb (d_wrap (setD_status FINISH_STATE s')) 0 = true).
    { change (d_wrap (setD_status FINISH_STATE s')) with (d_wrap s').
      rewrite FwS, Hwrapsd. reflexivity. }
    rewrite Ewleb in Hnone. cbv iota in Hnone.
    change (Z.eqb Z_STREAM_END Z_STREAM_END) with true in Hnone.
    cbv iota in Hnone.
    discriminate Hnone.
Qed.

(** Statement-honesty note (huffman-opt's flag): [zr_deflate_out] returns
    [[]] on the [defl_new]/[DfUnmodelled] arms.  Those arms CANNOT satisfy
    lemma 2's conclusion — the raw bound is at least 7 ([zr_bound_lo_raw])
    while [zlen [] = 0] — so the theorem is provable only because the
    proof walks the live [DfRet] path: the arms' deadness under this call
    shape is CONTAINED in the Qed above, and the corollary below pins the
    non-vacuity explicitly. *)
Corollary zr_l1_raw_none_exact_nonvacuous : forall x,
  ZR_Input x ->
  zr_deflate 1 (-15) x = None ->
  zr_deflate_out 1 (-15) x <> [].
Proof.
  intros x HIn Hnone Hnil.
  pose proof (zr_l1_raw_none_exact x HIn Hnone) as E.
  rewrite Hnil in E.
  change (zlen []) with 0 in E.
  pose proof (zr_bound_lo_raw (zlen x) (SwDrain.zlen_nonneg x)).
  lia.
Qed.

(* ==========================================================================
   4.  The frozen walk-extension seam (spelling of record: the
       walks-deflate handoff note NOTE-from-huffman-opt-fastwalk-conjunct.md,
       md5 , RE-FROZEN per flow-lead FITNOTE-v2 md5 :
       new BsFloor premise after DsInv, exit conjunct BsFloor g s'
       appended).  When walks-deflate lands the extended
       deflate_fast_finish, the _holds forms close by one exact.
   ========================================================================== *)

(** BsFloor now resolves to an earlier development run's landed DfArm.BsFloor. *)

Definition DfFastEvX_STMT : Prop :=
  forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  BsFloor g s ->
  DfSide (d_ls s) ->
  0 <= zs_availout (d_strm s) ->
  exists bs s' evs,
    deflate_fast Z_FINISH s = (bs, s')
    /\ Forall (EvOk g wrap (zs_done (d_strm s'))) evs
    /\ EvChain evs (ts_bw (d_ts s)) (zs_out (d_strm s))
                   (zs_availout (d_strm s))
                   (ts_bw (d_ts s')) (zs_out (d_strm s'))
                   (zs_availout (d_strm s'))
    /\ zs_done (d_strm s') ++ zs_in (d_strm s')
       = zs_done (d_strm s) ++ zs_in (d_strm s)
    /\ (exists nd, zs_done (d_strm s') = zs_done (d_strm s) ++ nd)
    /\ ( (exists evs0 evf,
            evs = evs0 ++ [evf]
            /\ Forall (fun e => fe_last e = 0) evs0
            /\ fe_last evf = 1
            /\ EvTile evs (slid + ls_blockstart (d_ls s))
                          (zlen (zs_done (d_strm s')))
            /\ zs_in (d_strm s') = []
            /\ zs_done (d_strm s')
               = zs_done (d_strm s) ++ zs_in (d_strm s)
            /\ CkInv wrap (d_strm s')
            /\ zs_totalin (d_strm s') = zlen (zs_done (d_strm s'))
            /\ ( (bs = FinishStarted /\ zs_availout (d_strm s') = 0)
               \/ (bs = FinishDone /\ 1 <= zs_availout (d_strm s')) ))
       \/ (bs = NeedMore /\ zs_availout (d_strm s') = 0
           /\ Forall (fun e => fe_last e = 0) evs) )
    /\ d_wrap s' = d_wrap s
    /\ d_cfg s' = d_cfg s
    /\ (exists te, EvTile evs (slid + ls_blockstart (d_ls s)) te
                   /\ te <= zlen (zs_done (d_strm s')))
    /\ (0 < dg_level g -> DfSnap (d_ts s) ->
        DfSnap (d_ts s')
        /\ Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs)
    /\ (0 < dg_level g -> Forall (fun ev =>
         (fe_last ev = 0 -> ts_symnext (d_ts (fe_s ev)) = dg_sym_end g)
         /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
             dg_max_dist g < fe_end ev - fe_start ev)) evs)
    /\ BsFloor g s'.

(* ==========================================================================
   5.  The level-1 per-event budget thread: min-fits glue, budget +
       bwv/availout threading, chain induction.  Consumes l1-adversary's
       ZRL1FastNone/ZRL1Close (landed in-tree, l1-adversary authorship).
   ========================================================================== *)

Lemma zho_min_fits_ev : forall g wrap done ev,
  EvOk g wrap done ev ->
  dg_sym_end g <= 49149 ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  32506 < fe_end ev - fe_start ev ->
  zr_l1_min_fits (d_ts (fe_s ev)) (fe_end ev - fe_start ev).
Proof.
  intros g wrap done ev HE Hsend Hol Hsl Hbl HblZ HnnL HnnD Hsld.
  destruct HE as (Ecfg & Ewrap & Hbuf & Hfreq & Henc & Hsn & Hspan & Hend
                  & Hres & Hspan_eq & Hwin & Hlast01).
  assert (Hlen : Z.of_nat (length (fe_toks ev)) <= 16383).
  { pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext. lia. }
  assert (Hext0 : toks_ext (fe_toks ev) = fe_end ev - fe_start ev).
  { pose proof (resolve_length (fe_toks ev)
                  (firstn (Z.to_nat (fe_start ev)) done)
                  (firstn (Z.to_nat (fe_end ev)) done) Henc Hres) as RL.
    rewrite !g6_zlen_firstn in RL by lia.
    lia. }
  exact (zr_l1_min_fits_holds (d_ts (fe_s ev)) (fe_toks ev)
           (fe_end ev - fe_start ev) Henc Hlen Hext0 Hsld
           Hol Hsl Hbl Hfreq HblZ HnnL HnnD).
Qed.

Lemma zho_acct_thread_fast : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g -> dg_strategy g = 0 -> dg_sym_end g <= 49149 ->
  bwv (ts_bw (d_ts (fe_s ev))) ->
  0 <= zs_availout (d_strm (fe_s ev)) ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  (ls_blockstart (d_ls (fe_s ev)) < 0 -> 32506 < fe_end ev - fe_start ev) ->
  EvStepBudget ev
  /\ bwv (ts_bw (d_ts (flush_block_only (fe_last ev) (fe_s ev))))
  /\ 0 <= zs_availout (d_strm (flush_block_only (fe_last ev) (fe_s ev))).
Proof.
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hol Hsl Hbl
         HblZ HnnL HnnD Hsld.
  assert (HB : EvStepBudget ev).
  { apply (flush_from_acct_full_fast g wrap done ev HE Hlev Hstrat Hsend
             Hbwv Havo Hol Hsl Hbl HblZ HnnL HnnD).
    intro Hlt.
    split; [exact (Hsld Hlt)|].
    exact (zho_min_fits_ev g wrap done ev HE Hsend Hol Hsl Hbl HblZ
             HnnL HnnD (Hsld Hlt)). }
  destruct (Z.le_gt_cases 0 (ls_blockstart (d_ls (fe_s ev)))) as [Hge|Hlt].
  - destruct (flush_block_only_acct g wrap done ev HE Hlev Hstrat Hsend
                Hbwv Havo Hge Hol Hsl Hbl HblZ HnnL HnnD)
      as (_ & _ & Hbwv' & _ & _ & Havo').
    exact (conj HB (conj Hbwv' Havo')).
  - destruct (flush_block_only_acct_none_fast g wrap done ev HE Hlev Hstrat
                Hsend Hbwv Havo Hlt (Hsld Hlt) Hol Hsl Hbl HblZ HnnL HnnD
                (zho_min_fits_ev g wrap done ev HE Hsend Hol Hsl Hbl HblZ
                   HnnL HnnD (Hsld Hlt)))
      as (_ & _ & Hbwv' & _ & _ & Havo').
    exact (conj HB (conj Hbwv' Havo')).
Qed.

Lemma zho_evchain_budget_fast :
  forall g wrap done evs bw out avo bw' out' avo',
  EvChain evs bw out avo bw' out' avo' ->
  Forall (EvOk g wrap done) evs ->
  Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs ->
  Forall (fun ev => ls_blockstart (d_ls (fe_s ev)) < 0 ->
                    dg_max_dist g < fe_end ev - fe_start ev) evs ->
  0 < dg_level g -> dg_strategy g = 0 -> dg_sym_end g <= 49149 ->
  dg_max_dist g = 32506 ->
  bwv bw -> 0 <= avo ->
  Forall EvStepBudget evs.
Proof.
  intros g wrap done evs.
  induction evs as [|ev r IH];
    intros bw out avo bw' out' avo' HCh HOk HSn HSld Hlev Hstrat Hsend
           Hmaxd Hbwv Havo.
  - constructor.
  - cbn [EvChain] in HCh.
    destruct HCh as (Hbw & Hout & Havoe & HCh').
    pose proof (Forall_inv HOk) as HOk1.
    pose proof (Forall_inv_tail HOk) as HOkr.
    pose proof (Forall_inv HSn) as HSn1.
    pose proof (Forall_inv_tail HSn) as HSnr.
    pose proof (Forall_inv HSld) as HSld1.
    pose proof (Forall_inv_tail HSld) as HSldr.
    destruct HSn1 as (HTI & Hol & Hsl).
    destruct HTI as (Hbl & HblZ & HnnL & HnnD & _).
    assert (HblZ' : forall v, 0 <= v < 19 ->
              t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0)
      by (intros v Hv; apply HblZ; change BL_CODES with 19; lia).
    destruct (zho_acct_thread_fast g wrap done ev HOk1 Hlev Hstrat Hsend
                ltac:(rewrite Hbw; exact Hbwv)
                ltac:(rewrite Havoe; exact Havo)
                Hol Hsl Hbl HblZ' HnnL HnnD
                ltac:(intro Hb; rewrite <- Hmaxd; exact (HSld1 Hb)))
      as (HB & Hbwv' & Havo').
    constructor; [exact HB|].
    exact (IH _ _ _ bw' out' avo' HCh' HOkr HSnr HSldr Hlev Hstrat Hsend
             Hmaxd Hbwv' Havo').
Qed.

(* ==========================================================================
   6.  LEMMA 1 (modulo the walk seam): one call at avail_out = bound + 1
       always succeeds within the bound, with bytes and the raw frame.
   ========================================================================== *)

Theorem zr_l1_raw_room1_of :
  DfFastEvX_STMT ->
  forall x, ZR_Input x ->
    exists enc, zr_deflate_room 1 1 (-15) x = Some enc
             /\ zlen enc <= zr_deflate_bound (-15) (zlen x)
             /\ Forall (fun b => 0 <= b < 256) enc
             /\ ZR_FramedRaw enc x.
Proof.
  intros HX x HIn.
  destruct HIn as (Hx & Hcap).
  destruct zr_g1m15_facts
    as (g & Eg & Hlvl & Hstrat & Hwrapg & Hse & _ & _ & _ & _ & Hgeom).
  (* dg_max_dist = 32506 at this config: the same vm step l1-adversary
     certified in their bed's DgMaxDistProbe.v (not yet landed in-tree;
     one-exact swap to their constant when it lands). *)
  assert (Hmaxd : dg_max_dist g = 32506).
  { assert (Eg' := Eg). vm_compute in Eg'. injection Eg' as Eg'.
    rewrite <- Eg'. reflexivity. }
  unfold zr_deflate_room, ZR_STRATEGY, defl_new.
  rewrite Eg. cbv iota.
  rewrite Hwrapg. cbv zeta.
  set (s1 := setD_strm
               (setZ_availout (zr_deflate_bound (-15) (zlen x) + 1)
                  (setZ_in x (d_strm (deflate_reset g 0))))
               (deflate_reset g 0)) in *.
  pose proof (SwDrain.zlen_nonneg x) as Hxn.
  pose proof (zr_bound_lo_raw (zlen x) Hxn) as HB.
  (* the entry *)
  assert (Hst1 : d_status s1 = INIT_STATE) by (vm_compute; reflexivity).
  assert (Havo1 : zs_availout (d_strm s1)
                  = zr_deflate_bound (-15) (zlen x) + 1)
    by (unfold s1; dsimp; reflexivity).
  assert (Hbw1 : bw_out (ts_bw (d_ts s1)) = [])
    by (vm_compute; reflexivity).
  rewrite (deflate_entry s1
             ltac:(rewrite Hst1; intro K; discriminate K)
             ltac:(rewrite Havo1; lia)
             Hbw1).
  rewrite (deflate_body_raw (setD_lastflush Z_FINISH s1)
             ltac:(dsimp; exact Hst1)
             ltac:(dsimp; unfold s1; dsimp; vm_compute; reflexivity)).
  set (sd := setD_status BUSY_STATE (setD_lastflush Z_FINISH s1)) in *.
  (* facts at the dispatch state *)
  assert (Hcfgsd : d_cfg sd = g) by (vm_compute; reflexivity).
  assert (Hwrapsd : d_wrap sd = 0) by (vm_compute; reflexivity).
  assert (Hstatsd : d_status sd = BUSY_STATE) by (vm_compute; reflexivity).
  assert (Hlssd : d_ls sd = d_ls (deflate_reset g 0))
    by (vm_compute; reflexivity).
  assert (Hbs0 : ls_blockstart (d_ls sd) = 0)
    by (rewrite Hlssd; vm_compute; reflexivity).
  assert (Houtsd : zs_out (d_strm sd) = [])
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Havosd : zs_availout (d_strm sd)
                   = zr_deflate_bound (-15) (zlen x) + 1)
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Hinsd : zs_in (d_strm sd) = x)
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Hdnsd : zs_done (d_strm sd) = [])
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Fbw : bw_out (ts_bw (d_ts sd)) = [])
    by (vm_compute; reflexivity).
  assert (Fbv : bw_valid (ts_bw (d_ts sd)) = 0)
    by (vm_compute; reflexivity).
  assert (Hbufsd : bw_buf (ts_bw (d_ts sd)) = 0)
    by (vm_compute; reflexivity).
  (* DsInv + DfSide + DfSnap at the dispatch state *)
  assert (HI : DsInv g 0 0 (fun _ => False) [] sd).
  { apply (dsinv_init g 15 15 0 x sd Hgeom).
    - exact Hcfgsd.
    - exact Hwrapsd.
    - exact Hlssd.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - exact Hinsd.
    - exact Hdnsd.
    - unfold sd, s1; dsimp; reflexivity.
    - split; intros K; discriminate K.
    - exact Hx. }
  assert (HSide : DfSide (d_ls sd)).
  { refine (conj _ (conj _ _)).
    - rewrite Hlssd. vm_compute. reflexivity.
    - rewrite Hlssd. vm_compute. reflexivity.
    - right. rewrite Hlssd. vm_compute. reflexivity. }
  assert (HSnapsd : DfSnap (d_ts sd)).
  { refine (conj _ (conj _ _)).
    - assert (E : d_ts sd = tr_init ts_new) by (vm_compute; reflexivity).
      rewrite E. exact treeinv_init.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity. }
  (* the extended walk (the frozen seam) *)
  assert (Havosd0 : 0 <= zs_availout (d_strm sd)) by (rewrite Havosd; lia).
  assert (HBsF : BsFloor g sd).
  { unfold BsFloor. rewrite Hbs0. intro K. lia. }
  destruct (HX g 15 15 0 0 (fun _ => False) [] sd
              Hgeom HI HBsF HSide Havosd0)
    as (bs & s' & evs & Efast & HFor & HCh & Hcons & Hdnx & Hout & FwS
        & FcS & Htile2 & HSnapw & HEvX & HBsF').
  assert (Edisp : dispatch Z_FINISH sd = (bs, s')).
  { rewrite (dispatch_fast sd).
    - exact Efast.
    - rewrite Hcfgsd, Hlvl. lia.
    - rewrite Hcfgsd. exact Hstrat. }
  rewrite (deflate_run_arm sd bs s' Hstatsd Edisp).
  (* the snap and seam threads, instantiated at level 1 *)
  destruct (HSnapw ltac:(rewrite Hlvl; lia) HSnapsd) as (HSn' & HSevs).
  pose proof (HEvX ltac:(rewrite Hlvl; lia)) as HXevs.
  assert (HSnX : Forall (fun ev => fe_last ev = 0 ->
                    ts_symnext (d_ts (fe_s ev)) = dg_sym_end g) evs)
    by (eapply Forall_impl; [|exact HXevs]; intros ev HP; exact (proj1 HP)).
  assert (HSldX : Forall (fun ev => ls_blockstart (d_ls (fe_s ev)) < 0 ->
                    dg_max_dist g < fe_end ev - fe_start ev) evs)
    by (eapply Forall_impl; [|exact HXevs]; intros ev HP; exact (proj2 HP)).
  (* per-event budgets *)
  assert (Hbwv0 : bwv (ts_bw (d_ts sd)))
    by (unfold bwv; rewrite Fbv; unfold Buf_size; lia).
  pose proof (zho_evchain_budget_fast g 0 (zs_done (d_strm s')) evs
                _ _ _ _ _ _ HCh HFor HSevs HSldX
                ltac:(rewrite Hlvl; lia) Hstrat ltac:(rewrite Hse; lia)
                Hmaxd Hbwv0 Havosd0) as HBud.
  (* the tile from 0 *)
  destruct Htile2 as (te & Htile0 & Hte).
  assert (Htile : EvTile evs 0 te).
  { replace 0 with (0 + ls_blockstart (d_ls sd)) by (rewrite Hbs0; lia).
    exact Htile0. }
  assert (Hsp0 : Forall (fun ev => 0 <= fe_end ev - fe_start ev) evs).
  { eapply Forall_impl; [|exact HFor].
    intros ev HE.
    destruct HE as (_ & _ & _ & _ & _ & _ & Hspan & _). lia. }
  assert (Hte0 : 0 <= te)
    by (pose proof (evtile_nonneg evs 0 te Htile Hsp0); lia).
  assert (Hdone_le : zlen (zs_done (d_strm s')) <= zlen x).
  { rewrite Hdnsd, Hinsd in Hcons. cbn [app] in Hcons.
    rewrite <- Hcons, g6_zlen_app.
    pose proof (SwDrain.zlen_nonneg (zs_in (d_strm s'))).
    lia. }
  assert (HT : 0 <= te <= zlen x) by lia.
  assert (Esym : dg_sym_end g = 49149) by exact Hse.
  (* the block count *)
  assert (Hblocks : Z.of_nat (length evs) <= zr_hnblocks (zlen x)).
  { unfold zr_hnblocks.
    destruct Hout as [HL | HR].
    - destruct HL as (evs0 & evf & Ee & H0s & Hl1 & _ & _ & _ & _ & _ & _).
      subst evs.
      destruct (evtile_split evs0 [evf] 0 te Htile) as (m & Ht0 & Ht1).
      assert (HFull : Forall (fun ev => 16383 <= fe_end ev - fe_start ev)
                        evs0).
      { rewrite Forall_forall. intros ev Hin.
        rewrite Forall_forall in HFor, HSnX, H0s.
        assert (Hin' : In ev (evs0 ++ [evf]))
          by (apply in_or_app; left; exact Hin).
        exact (evsnap_min_span g 0 (zs_done (d_strm s')) ev (HFor ev Hin')
                 Esym (HSnX ev Hin') (H0s ev Hin)). }
      pose proof (evtile_full_count evs0 0 m Ht0 HFull) as Hcnt.
      cbn [EvTile] in Ht1. destruct Ht1 as [Hm Hte'].
      assert (Hmf : 0 <= fe_end evf - fe_start evf).
      { rewrite Forall_forall in Hsp0.
        apply Hsp0. apply in_or_app. right. left. reflexivity. }
      rewrite length_app. cbn [length].
      rewrite Nat2Z.inj_add.
      assert (Hq : Z.of_nat (length evs0) <= zlen x / 16383).
      { apply Z.div_le_lower_bound; lia. }
      cbn [Z.of_nat]. lia.
    - destruct HR as (_ & _ & H0all).
      assert (HFull : Forall (fun ev => 16383 <= fe_end ev - fe_start ev)
                        evs).
      { rewrite Forall_forall. intros ev Hin.
        rewrite Forall_forall in HFor, HSnX, H0all.
        exact (evsnap_min_span g 0 (zs_done (d_strm s')) ev (HFor ev Hin)
                 Esym (HSnX ev Hin) (H0all ev Hin)). }
      pose proof (evtile_full_count evs 0 te Htile HFull) as Hcnt.
      assert (Hq : Z.of_nat (length evs) <= zlen x / 16383).
      { apply Z.div_le_lower_bound; lia. }
      lia. }
  (* the fits ledger at (B = bound + 1, hdr = 0, troom = 1) *)
  assert (H1avo : 1 <= zs_availout (d_strm s')).
  { refine (zr_bound_fits_p x evs (ts_bw (d_ts sd)) (ts_bw (d_ts s'))
             (zs_out (d_strm sd)) (zs_out (d_strm s'))
             (zs_availout (d_strm sd)) (zs_availout (d_strm s'))
             (zr_deflate_bound (-15) (zlen x) + 1) 0 1
             (conj Hxn Hcap)
             HCh te HT Htile HBud Hblocks
             _ _ _ _).
    - rewrite Houtsd. reflexivity.
    - rewrite (zbits_eqn _ ltac:(rewrite Fbv; lia)).
      rewrite Fbw, Fbv. reflexivity.
    - rewrite Havosd. ring.
    - unfold zr_deflate_bound, zr_wraplen.
      replace (Z.ltb (-15) 0) with true by reflexivity.
      rewrite !Z.shiftr_div_pow2 by lia.
      replace (2 ^ 12) with 4096 by reflexivity.
      replace (2 ^ 14) with 16384 by reflexivity.
      replace (2 ^ 25) with 33554432 by reflexivity.
      pose proof (zr_room_shifts (zlen x)
                    ltac:(unfold ZR_MAX_INPUT in Hcap; lia)) as Hr.
      lia. }
  (* the outcome: the exhausted arms are refuted, FinishDone remains *)
  destruct Hout as [HL | HR].
  2:{ destruct HR as (_ & Eav0 & _). exfalso. lia. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & Htilez & Ein' & Edone'
                  & HK & Hti' & Hbs2).
  destruct Hbs2 as [(Ebs & Eav0)|(Ebs & Hav1)].
  { exfalso. lia. }
  rewrite Ebs.
  cbv iota.
  assert (Ewleb : Z.leb (d_wrap (setD_status FINISH_STATE s')) 0 = true).
  { change (d_wrap (setD_status FINISH_STATE s')) with (d_wrap s').
    rewrite FwS, Hwrapsd. reflexivity. }
  rewrite Ewleb. cbv iota.
  change (Z.eqb Z_STREAM_END Z_STREAM_END) with true.
  cbv iota.
  change (zs_out (d_strm (setD_status FINISH_STATE s')))
    with (zs_out (d_strm s')).
  exists (zs_out (d_strm s')).
  split; [reflexivity|].
  (* the bound: conservation *)
  destruct (zho_evchain_avail_eq evs _ _ _ _ _ _ HCh Havosd0)
    as (_ & Hsum).
  rewrite Houtsd, Havosd in Hsum.
  change (zlen []) with 0 in Hsum.
  split; [lia|].
  (* byte range *)
  assert (Hbytes : Forall (fun b => 0 <= b < 256) (zs_out (d_strm s'))).
  { destruct (evchain_out_bytes evs _ _ _ _ _ _ HCh
                ltac:(unfold BwBytes; rewrite Fbw; constructor)
                ltac:(rewrite Houtsd; constructor))
      as (Hout' & _).
    exact Hout'. }
  split; [exact Hbytes|].
  (* the frame: input fully consumed, then the decode engine *)
  assert (Edx : zs_done (d_strm s') = x)
    by (rewrite Edone', Hdnsd, Hinsd; reflexivity).
  assert (HSpan : Forall ZR_SpanGuard evs).
  { rewrite Ee in HFor, HSevs |- *.
    apply Forall_forall. intros ev Hin.
    assert (HOev : EvOk g 0 (zs_done (d_strm s')) ev)
      by (exact (proj1 (Forall_forall _ _) HFor ev Hin)).
    assert (HSev : DfSnap (d_ts (fe_s ev)))
      by (exact (proj1 (Forall_forall _ _) HSevs ev Hin)).
    destruct HSev as (HT' & Ho & Hst).
    destruct HT' as (Hblc & Hblf & HdlL & HdlD & HdlBL).
    apply (span_guard_holds g 0 (zs_done (d_strm s')) ev HOev
             ltac:(rewrite Hlvl; lia)
             ltac:(rewrite Hse; lia)
             Ho Hst Hblc
             ltac:(intros v Hv; apply Hblf; unfold BL_CODES; exact Hv)
             HdlL HdlD). }
  assert (HDyn : Forall (fun e => ZR_DynEntry (d_ts (fe_s e))) evs).
  { apply Forall_forall. intros ev Hin.
    assert (HSev : DfSnap (d_ts (fe_s ev)))
      by (exact (proj1 (Forall_forall _ _) HSevs ev Hin)).
    destruct HSev as (HT' & _ & _).
    apply treeinv_dynentry.
    - exact HT'.
    - destruct HT' as (_ & Hblf & _).
      intros i Hi. apply Hblf. unfold BL_CODES. exact Hi.
    - apply maxcd_all. }
  rewrite Ee in HFor, HCh, HSpan, HDyn.
  pose proof (body_decodes g 0 x sd s' evs0 evf (zs_out (d_strm s')) []
           ltac:(rewrite Hlvl; lia) Hx HFor HCh
           Houtsd Fbw Fbv Hbufsd
           ltac:(rewrite Havosd; lia)
           H0s Hl1
           ltac:(rewrite <- Ee;
                 replace 0 with (0 + ls_blockstart (d_ls sd))
                   at 1 by (rewrite Hbs0; lia);
                 exact Htilez)
           Edx
           ltac:(cbn [app]; reflexivity)
           ltac:(lia)
           HSpan HDyn) as BD.
  exact (proj1 BD).
Qed.

(* ==========================================================================
   7.  The seam is LANDED: the unconditional counterfactual face.
   ========================================================================== *)

Theorem zr_l1_raw_room1 :
  forall x, ZR_Input x ->
    exists enc, zr_deflate_room 1 1 (-15) x = Some enc
             /\ zlen enc <= zr_deflate_bound (-15) (zlen x)
             /\ Forall (fun b => 0 <= b < 256) enc
             /\ ZR_FramedRaw enc x.
Proof.
  exact (zr_l1_raw_room1_of DfFast.deflate_fast_finish).
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions zr_l1_raw_none_exact.
Print Assumptions zr_l1_raw_none_exact_nonvacuous.
Print Assumptions zr_l1_raw_room1_of.
Print Assumptions zr_l1_raw_room1.
Unset Printing All.
