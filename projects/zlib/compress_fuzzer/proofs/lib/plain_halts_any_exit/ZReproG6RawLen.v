(** * ZReproG6RawLen — Hrawlen: the raw (1,-15) enc-length bound (GAP7 F6).

    TL commission (g6-bound lane, 2026-08-21), q7-decode's consumer
    spelling verbatim:

        ZR_Input x -> zr_deflate 1 (-15) x = Some enc
                   -> zlen enc <= 4294967290.

    SCOPE FENCE: this is the LOOSE ceiling only.  The tight deflateBound
    l1 fit (R41) stays an earlier development run's; nothing here touches TOO_FAR /
    es_far, tally accounting, or per-token costs.

    ROUTE (leaner than commissioned — the crude token budget collapsed):
    the model's [flush_pending] drain is MIN-CLAMPED, so across every
    flush event availout decrements by EXACTLY the output growth and
    stays nonnegative.  Folding that conservation law along the EvChain
    that [deflate_fast_finish] (q5's dfast corpus) publishes gives
        zlen (zs_out final) <= initial availout
    with NO per-event content facts at all; the entry sets availout to
    [zr_deflate_bound (-15) (zlen x)], and [zr_bound_small] caps that at
    4294967290 under ZR_Input's 64MiB bound.  The bridge from
    [zr_deflate] to the fast-path run is replayed verbatim from
    ZRRawShell.zr_emitter_l1_raw_frame (q5's landed decomposition),
    trimmed of the snap/span/decode threads this bound does not need. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre
  SwDrain SwInit SwStep SwLoop SwTail SwSlow G5Chain ZRTreeState ZREvSnap
  ZRThread ZREmitBody ZREmitBytes ZReproG6O ZREmitShell
  DfArm DfIns DfArm1 DfArm2 DfStep DfLoop DfFast ZRRawShell.
Import SymbolIdDeclIface.
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
   1.  availout conservation across [flush_pending] — premise-free beyond
       nonnegativity: the drain length is min-clamped by construction.
   ========================================================================== *)

Lemma flush_pending_avail : forall s,
  0 <= zs_availout (d_strm s) ->
  zs_availout (d_strm (flush_pending s))
    = zs_availout (d_strm s)
      - (zlen (zs_out (d_strm (flush_pending s)))
         - zlen (zs_out (d_strm s)))
  /\ 0 <= zs_availout (d_strm (flush_pending s))
  /\ zlen (zs_out (d_strm s)) <= zlen (zs_out (d_strm (flush_pending s))).
Proof.
  intros s Ha.
  unfold flush_pending. cbv zeta.
  set (pd := bw_out (ts_bw (tr_flush_bits (d_ts s)))).
  pose proof (SwDrain.zlen_nonneg pd) as Hpd.
  set (len := if Z.ltb (zs_availout (d_strm s)) (zlen pd)
              then zs_availout (d_strm s) else zlen pd).
  assert (Hlen : 0 <= len <= zlen pd /\ len <= zs_availout (d_strm s)).
  { unfold len. destruct (Z.ltb (zs_availout (d_strm s)) (zlen pd)) eqn:El.
    - apply Z.ltb_lt in El. clear -Ha El. lia.
    - apply Z.ltb_ge in El. clear -Ha El Hpd. lia. }
  destruct Hlen as (Hl1 & Hl2).
  destruct (Z.eqb len 0) eqn:Ez.
  - (* no-op branch: only d_ts changes *)
    dsimp. split; [clear -Ha; lia|]. split; [exact Ha|]. clear; lia.
  - (* drain branch *)
    dsimp.
    rewrite ZREmitShell.zlen_app.
    rewrite (ZREmitShell.zlen_firstn_exact len pd Hl1).
    split; [clear -Hl2; lia|].
    split; [clear -Hl2; lia|].
    apply Z.eqb_neq in Ez. clear -Hl1 Ez. lia.
Qed.

(* ==========================================================================
   2.  the same across [flush_block_only]: the tr_flush_block/setter prefix
       never touches [zs_out]/[zs_availout].
   ========================================================================== *)

Lemma fbo_avail : forall last s,
  0 <= zs_availout (d_strm s) ->
  zs_availout (d_strm (flush_block_only last s))
    = zs_availout (d_strm s)
      - (zlen (zs_out (d_strm (flush_block_only last s)))
         - zlen (zs_out (d_strm s)))
  /\ 0 <= zs_availout (d_strm (flush_block_only last s))
  /\ zlen (zs_out (d_strm s))
     <= zlen (zs_out (d_strm (flush_block_only last s))).
Proof.
  intros last s Ha.
  unfold flush_block_only. cbv zeta.
  match goal with
  | |- context [flush_pending ?st] => set (s2 := st)
  end.
  assert (Eo : zs_out (d_strm s2) = zs_out (d_strm s))
    by (unfold s2; dsimp; reflexivity).
  assert (Ea : zs_availout (d_strm s2) = zs_availout (d_strm s))
    by (unfold s2; dsimp; reflexivity).
  destruct (flush_pending_avail s2 ltac:(rewrite Ea; exact Ha))
    as (E1 & E2 & E3).
  rewrite Eo, Ea in E1. rewrite Eo in E3.
  exact (conj E1 (conj E2 E3)).
Qed.

(* ==========================================================================
   3.  the fold: along any EvChain, output growth is paid from availout.
   ========================================================================== *)

Lemma evchain_avail : forall evs bw out avo bw' out' avo',
  EvChain evs bw out avo bw' out' avo' ->
  0 <= avo ->
  0 <= avo'
  /\ zlen out <= zlen out'
  /\ zlen out' + avo' <= zlen out + avo.
Proof.
  induction evs as [|ev r IH];
    intros bw out avo bw' out' avo' HCh Ha; cbn [EvChain] in HCh.
  - destruct HCh as (Eb & Eo & Ea). subst.
    split; [exact Ha|]. split; clear; lia.
  - destruct HCh as (Hbw & Hout & Havo & HCh').
    destruct (fbo_avail (fe_last ev) (fe_s ev)
                ltac:(rewrite Havo; exact Ha)) as (E1 & E2 & E3).
    destruct (IH _ _ _ _ _ _ HCh' E2) as (I1 & I2 & I3).
    rewrite Hout, Havo in E1. rewrite Hout in E3.
    split; [exact I1|].
    split; [clear -E3 I2; lia|].
    clear -E1 E3 I3. lia.
Qed.

(* ==========================================================================
   4.  Hrawlen — the bridge replayed from ZRRawShell (trimmed), then the
       conservation fold and [zr_bound_small].
   ========================================================================== *)

Theorem hrawlen : forall x enc,
  ZR_Input x ->
  zr_deflate 1 (-15) x = Some enc ->
  zlen enc <= 4294967290.
Proof.
  intros x enc (Hx & Hcap) Hsome.
  destruct zr_g1m15_facts
    as (g & Eg & Hlvl & Hstrat & Hwrapg & Hse & _ & _ & _ & _ & Hgeom).
  unfold zr_deflate, ZR_STRATEGY, defl_new in Hsome.
  rewrite Eg in Hsome. cbv iota in Hsome.
  rewrite Hwrapg in Hsome. cbv zeta in Hsome.
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
             Hbw1) in Hsome.
  (* the raw header phase: nothing, straight to BUSY *)
  rewrite (deflate_body_raw (setD_lastflush Z_FINISH s1)
             ltac:(dsimp; exact Hst1)
             ltac:(dsimp; unfold s1; dsimp; vm_compute; reflexivity))
    in Hsome.
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
  assert (HBsFsd : BsFloor g sd).
  { intros HBneg. exfalso.
    replace (ls_blockstart (d_ls sd)) with 0 in HBneg
      by (rewrite Hlssd; vm_compute; reflexivity).
    lia. }
  destruct (deflate_fast_finish g 15 15 0 0 (fun _ => False) [] sd
              Hgeom HI HBsFsd HSide Havosd0)
    as (bs & s' & evs & Efast & HFor & HCh & Hcons & Hdnx & Hout & FwS
        & FcS & Htile2 & HSnapw & _ & _).
  (* dispatch plumbing *)
  assert (Edisp : dispatch Z_FINISH sd = (bs, s')).
  { rewrite (dispatch_fast sd).
    - exact Efast.
    - rewrite Hcfgsd, Hlvl. lia.
    - rewrite Hcfgsd. exact Hstrat. }
  rewrite (deflate_run_arm sd bs s' Hstatsd Edisp) in Hsome.
  (* the outcome: Some pins FinishDone *)
  destruct Hout as [HL | HR].
  2:{ (* NeedMore: DfRet Z_OK, refuted by Some *)
      destruct HR as (Ebs & _ & _). rewrite Ebs in Hsome.
      destruct (Z.eqb (zs_availout (d_strm s')) 0);
        cbv iota in Hsome;
        vm_compute in Hsome; discriminate Hsome. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & Htile & Ein' & Edone'
                  & HK & Hti' & Hbs2).
  destruct Hbs2 as [(Ebs & Eav0)|(Ebs & Hav1)].
  { (* FinishStarted: DfRet Z_OK, refuted by Some *)
    rewrite Ebs in Hsome.
    destruct (Z.eqb (zs_availout (d_strm (setD_status FINISH_STATE s'))) 0);
      cbv iota in Hsome;
      vm_compute in Hsome; discriminate Hsome. }
  (* FinishDone at wrap <= 0: Z_STREAM_END with no trailer *)
  rewrite Ebs in Hsome.
  assert (Ewleb : Z.leb (d_wrap (setD_status FINISH_STATE s')) 0 = true).
  { change (d_wrap (setD_status FINISH_STATE s')) with (d_wrap s').
    rewrite FwS, Hwrapsd. reflexivity. }
  rewrite Ewleb in Hsome. cbv iota in Hsome.
  change (Z.eqb Z_STREAM_END Z_STREAM_END) with true in Hsome.
  cbv iota in Hsome.
  injection Hsome as Henc.
  change (zs_out (d_strm (setD_status FINISH_STATE s')))
    with (zs_out (d_strm s')) in Henc.
  (* THE CONSERVATION FOLD *)
  destruct (evchain_avail evs _ _ _ _ _ _ HCh Havosd0) as (Hav' & _ & Hsum).
  rewrite Houtsd, Havosd in Hsum.
  change (zlen []) with 0 in Hsum.
  pose proof (zr_bound_small (-15) (zlen x) (conj Hxn Hcap)) as Hsmall.
  rewrite <- Henc.
  clear -Hav' Hsum Hsmall. lia.
Qed.

Print Assumptions hrawlen.
