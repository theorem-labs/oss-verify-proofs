(** * ZRRawShell — the (1,-15) raw config's CONDITIONAL frame lemma
      (GAP7 D1's deliverable).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-21).

    THE SHAPE (q7-decode's shape-ACK, GAP7ACK): conditional on
    [zr_deflate 1 (-15) x = Some enc] — exactly what ZR_PumpSucceeds
    premises — so the R41-open fast-path bound-fit question never
    enters: [Some] hands us the FinishDone walk, and the raw stream IS
    the deflate body ([hdr = []], no trailer at wrap 0).

    The full face [ZRepro_Emitter_l1_raw] (existence for ALL inputs)
    remains R41-open (its [Some] conjunct is the bound-fit); see the
    a5 F-row scope flag.  Nothing here touches that question. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre
  SwDrain SwInit SwStep SwLoop SwTail SwSlow G5Chain ZRTreeState ZREvSnap
  ZRThread ZREmitBody ZREmitBytes ZReproG6O
  DfArm DfIns DfArm1 DfArm2 DfStep DfLoop DfFast Gap7Strict.
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

(** The (1,-15) geometry facts, vm-extracted. *)
Lemma zr_g1m15_facts : exists g,
  defl_init2 1 8 (-15) 8 0 = Some g
  /\ dg_level g = 1
  /\ dg_strategy g = 0
  /\ dg_wrap g = 0
  /\ dg_sym_end g = 49149
  /\ dg_max_lazy_match g = 4
  /\ dg_max_chain_length g = 4
  /\ dg_good_match g = 4
  /\ dg_nice_match g = 8
  /\ GeomOk2 g 15 15.
Proof.
  destruct (defl_init2 1 8 (-15) 8 0) as [g|] eqn:Eg.
  - exists g.
    assert (Eg' := Eg). vm_compute in Eg'.
    injection Eg' as Eg''. subst g.
    split; [exact Eg|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    pose proof swtally_geom2_zr as G.
    vm_compute in G.
    exact (proj1 (proj2 G)).
  - vm_compute in Eg. discriminate Eg.
Qed.

(** The raw bound has at least the constant headroom. *)
Lemma zr_bound_lo_raw : forall n, 0 <= n -> 7 <= zr_deflate_bound (-15) n.
Proof.
  intros n Hn.
  unfold zr_deflate_bound.
  change (zr_wraplen (-15)) with 0.
  pose proof (proj2 (Z.shiftr_nonneg n 12) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 14) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 25) Hn).
  lia.
Qed.

(** A2-raw: at INIT with wrap 0 the body emits nothing and goes BUSY. *)
Lemma deflate_body_raw : forall s,
  d_status s = INIT_STATE ->
  d_wrap s = 0 ->
  deflate_body Z_FINISH s
  = deflate_run Z_FINISH (setD_status BUSY_STATE s).
Proof.
  intros s Hst Hwrap.
  unfold deflate_body. cbv zeta.
  rewrite Hst, Hwrap.
  change (Z.eqb INIT_STATE FINISH_STATE) with false.
  change (Z.eqb INIT_STATE INIT_STATE) with true.
  change (Z.eqb 0 0) with true.
  cbn [andb negb]. cbv iota.
  dsimp.
  change (Z.eqb BUSY_STATE INIT_STATE) with false. cbv iota.
  change (Z.eqb BUSY_STATE GZIP_STATE) with false. cbv iota.
  reflexivity.
Qed.

(** A3-raw: levels 1-3 dispatch to [deflate_fast]. *)
Lemma dispatch_fast : forall s,
  1 <= dg_level (d_cfg s) <= 3 ->
  dg_strategy (d_cfg s) = 0 ->
  dispatch Z_FINISH s = deflate_fast Z_FINISH s.
Proof.
  intros s Hl Hstrat.
  unfold dispatch. cbv zeta.
  rewrite (proj2 (Z.eqb_neq (dg_level (d_cfg s)) 0) ltac:(lia)).
  rewrite Hstrat.
  change (Z.eqb 0 Z_HUFFMAN_ONLY) with false.
  change (Z.eqb 0 Z_RLE) with false.
  cbv iota.
  unfold cfg_func.
  rewrite (proj2 (Z.eqb_neq (dg_level (d_cfg s)) 0) ltac:(lia)).
  rewrite (proj2 (Z.leb_le (dg_level (d_cfg s)) 3) ltac:(lia)).
  cbv iota. reflexivity.
Qed.

(** THE CONDITIONAL FRAME LEMMA (Pump_l1_raw's input). *)
Theorem zr_emitter_l1_raw_frame : forall x enc,
  ZR_Input x ->
  zr_deflate 1 (-15) x = Some enc ->
  Forall (fun b => 0 <= b < 256) enc /\ BodyDecodesTo enc x
  /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
      exists rem, dec_stream_from_strict (bytes_bits enc) []
                  = Some (x, rem)).
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
  pose proof (zlen_nonneg x) as Hxn.
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
  assert (Hbs0 : ls_blockstart (d_ls sd) = 0)
    by (rewrite Hlssd; vm_compute; reflexivity).
  assert (Houtsd : zs_out (d_strm sd) = [])
    by (unfold sd, s1; dsimp; reflexivity).
  assert (Havosd : zs_availout (d_strm sd)
                   = zr_deflate_bound (-15) (zlen x))
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
  (* the input is fully consumed *)
  assert (Edx : zs_done (d_strm s') = x)
    by (rewrite Edone', Hdnsd, Hinsd; reflexivity).
  (* the snap thread, instantiated *)
  destruct (HSnapw ltac:(rewrite Hlvl; lia) HSnapsd) as (HSn' & HSevs).
  (* the per-event SpanGuard / DynEntry Foralls from the snaps *)
  assert (HSpan : Forall ZR_SpanGuard evs).
  { rewrite Ee in HFor, HSevs |- *.
    apply Forall_forall. intros ev Hin.
    assert (HOev : EvOk g 0 (zs_done (d_strm s')) ev)
      by (exact (proj1 (Forall_forall _ _) HFor ev Hin)).
    assert (HSev : DfSnap (d_ts (fe_s ev)))
      by (exact (proj1 (Forall_forall _ _) HSevs ev Hin)).
    destruct HSev as (HT & Ho & Hst).
    destruct HT as (Hblc & Hblf & HdlL & HdlD & HdlBL).
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
    destruct HSev as (HT & _ & _).
    apply treeinv_dynentry.
    - exact HT.
    - destruct HT as (_ & Hblf & _).
      intros i Hi. apply Hblf. unfold BL_CODES. exact Hi.
    - apply maxcd_all. }
  (* byte range on the output *)
  assert (Hbytes : Forall (fun b => 0 <= b < 256) enc).
  { rewrite <- Henc.
    destruct (evchain_out_bytes evs _ _ _ _ _ _ HCh
                ltac:(unfold BwBytes; rewrite Fbw; constructor)
                ltac:(rewrite Houtsd; constructor))
      as (Hout' & _).
    exact Hout'. }
  split; [exact Hbytes|].
  (* the decode: hdr = [], body = enc *)
  rewrite Ee in HFor, HCh, HSpan, HDyn.
  pose proof (body_decodes g 0 x sd s' evs0 evf enc []
           ltac:(rewrite Hlvl; lia) Hx HFor HCh
           Houtsd Fbw Fbv Hbufsd
           ltac:(rewrite Havosd; lia)
           H0s Hl1
           ltac:(rewrite <- Ee;
                 replace 0 with (0 + ls_blockstart (d_ls sd))
                   at 1 by (rewrite Hbs0; lia);
                 exact Htile)
           Edx
           ltac:(cbn [app]; exact Henc)
           ltac:(lia)
           HSpan HDyn) as BD.
  split; [exact (proj1 BD)|].
  intros HBK EFR.
  destruct (proj2 (proj2 BD) HBK EFR) as (rem & Hst & _).
  exists rem. exact Hst.
Qed.

Print Assumptions zr_emitter_l1_raw_frame.
