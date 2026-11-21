(** * ZRGzShell — the (9, 31) gzip emitter shell.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The gzip mirror of ZREmitShell.emitter_shell: one [zr_deflate 9 31 x]
    call unrolled — GZIP entry state, the ten header bytes (ZREmitGz),
    the wrap-generic walk pack, the tree-state invariant, and — under the
    bound seam ([bs = FinishDone] with [8 <= avail_out] for the
    CRC32+ISIZE trailer) — the [Some enc] equation. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwStep SwDrain
  SwInit SwSlow G5Chain ZRTreeState ZREvSnap ZREmitShell ZREmitGz.
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

(* fastshadow: put_byte-level wrappers keep the gzip-header-tower proof terms
   and their kernel conversions in FOLDED put_byte form. The set_bw-level lemmas
   force `unfold put_byte` (tower duplication, 2^10 x base) and a final
   ZRTreeInv conversion the kernel re-derives exponentially (measured 255.9s at
   Validate Proof); the wrappers keep it linear and near-syntactic. *)
Local Lemma treeinv_putbyte : forall v ts,
  ZRTreeInv ts -> ZRTreeInv (put_byte v ts).
Proof. intros v ts H. unfold put_byte. apply treeinv_setbw. exact H. Qed.

Local Lemma statzero_putbyte : forall v ts,
  ts_optlen ts = 0 /\ ts_statlen ts = 0 ->
  ts_optlen (put_byte v ts) = 0 /\ ts_statlen (put_byte v ts) = 0.
Proof. intros v ts H. unfold put_byte. apply statzero_setbw. exact H. Qed.

(* ==========================================================================
   1.  The (9, 31) config, by value.
   ========================================================================== *)

Lemma zr_g931_facts : exists g,
  defl_init2 9 8 31 8 0 = Some g
  /\ dg_level g = 9
  /\ dg_strategy g = 0
  /\ dg_wrap g = 2
  /\ dg_w_bits g = 15
  /\ GeomOk2 g 15 15.
Proof.
  destruct (defl_init2 9 8 31 8 0) as [g|] eqn:Eg.
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
    exact (proj1 (proj2 (proj2 G))).
  - vm_compute in Eg. discriminate Eg.
Qed.

(* ==========================================================================
   6.  The shell: one [zr_deflate ZR_DEFAULT_LEVEL 15] call, unrolled to
       the walk pack, with the trailer under the G6 seam.
   ========================================================================== *)

Theorem emitter_shell_gz : forall x,
  Forall (fun b => 0 <= b < 256) x ->
  exists g sd bs s' evs,
    defl_init2 9 8 31 8 0 = Some g
    /\ dg_level g = 9
    /\ dg_strategy g = 0
    /\ dg_w_bits g = 15
    /\ GeomOk2 g 15 15
    /\ deflate_slow Z_FINISH sd = (bs, s')
    /\ d_cfg sd = g
    /\ d_wrap sd = 2
    /\ zs_out (d_strm sd) = [31; 139; 8; 0; 0; 0; 0; 0; 2; 3]
    /\ zs_availout (d_strm sd) = zr_deflate_bound 31 (zlen x) - 10
    /\ zs_in (d_strm sd) = x
    /\ zs_done (d_strm sd) = []
    /\ bw_out (ts_bw (d_ts sd)) = []
    /\ bw_valid (ts_bw (d_ts sd)) = 0
    /\ bw_buf (ts_bw (d_ts sd)) = 0
    /\ DsInv g 2 0 (fun _ => False) [] sd
    /\ Forall (EvOk g 2 (zs_done (d_strm s'))) evs
    /\ EvChain evs (ts_bw (d_ts sd)) (zs_out (d_strm sd))
                   (zs_availout (d_strm sd))
                   (ts_bw (d_ts s')) (zs_out (d_strm s'))
                   (zs_availout (d_strm s'))
    /\ zs_done (d_strm s') ++ zs_in (d_strm s') = x
    /\ d_wrap s' = 2
    /\ d_cfg s' = g
    /\ ( (exists evs0 evf,
            evs = evs0 ++ [evf]
            /\ Forall (fun e => fe_last e = 0) evs0
            /\ fe_last evf = 1
            /\ EvTile evs 0 (zlen (zs_done (d_strm s')))
            /\ zs_in (d_strm s') = []
            /\ zs_done (d_strm s') = x
            /\ CkInv 2 (d_strm s')
            /\ zs_totalin (d_strm s') = zlen x
            /\ ( (bs = FinishStarted /\ zs_availout (d_strm s') = 0)
               \/ (bs = FinishDone /\ 0 <= zs_availout (d_strm s')) ))
       \/ (bs = NeedMore /\ zs_availout (d_strm s') = 0
           /\ Forall (fun e => fe_last e = 0) evs) )
    /\ (bs = FinishDone -> 8 <= zs_availout (d_strm s') ->
        exists body,
          zs_out (d_strm s') = [31; 139; 8; 0; 0; 0; 0; 0; 2; 3] ++ body
          /\ zlen body = (zr_deflate_bound 31 (zlen x) - 10)
                         - zs_availout (d_strm s')
          /\ zr_deflate 9 31 x
             = Some ([31; 139; 8; 0; 0; 0; 0; 0; 2; 3] ++ body
                 ++ [u8 (zs_adler (d_strm s'));
                     u8 (Z.shiftr (zs_adler (d_strm s')) 8);
                     u8 (Z.shiftr (zs_adler (d_strm s')) 16);
                     u8 (Z.shiftr (zs_adler (d_strm s')) 24);
                     u8 (zs_totalin (d_strm s'));
                     u8 (Z.shiftr (zs_totalin (d_strm s')) 8);
                     u8 (Z.shiftr (zs_totalin (d_strm s')) 16);
                     u8 (Z.shiftr (zs_totalin (d_strm s')) 24)]))
    /\ (exists te, EvTile evs 0 te /\ te <= zlen (zs_done (d_strm s')))
    /\ ZRTreeInv (d_ts sd)
    /\ ZRTreeInv (d_ts s')
    /\ Forall (EvSnapOk g) evs
    /\ dg_max_dist g = 32506.
Proof.
  intros x Hx.
  destruct zr_g931_facts as (g & Eg & Hlvl & Hstrat & Hwrapg & Hwb & Hgeom).
  set (s1 := setD_strm
               (setZ_availout (zr_deflate_bound 31 (zlen x))
                  (setZ_in x (d_strm (deflate_reset g 2))))
               (deflate_reset g 2)).
  assert (HB : 25 <= zr_deflate_bound 31 (zlen x)).
  { unfold zr_deflate_bound.
    change (zr_wraplen 31) with 18.
    pose proof (zlen_nonneg x) as Hz0.
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 12) Hz0).
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 14) Hz0).
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 25) Hz0).
    lia. }
  assert (Hst1 : d_status s1 = GZIP_STATE) by reflexivity.
  assert (Hwr1 : d_wrap s1 = 2) by reflexivity.
  assert (Hcfg1 : d_cfg s1 = g) by reflexivity.
  assert (Havo1 : zs_availout (d_strm s1) = zr_deflate_bound 31 (zlen x))
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
    - rewrite Hst1. unfold GZIP_STATE, FINISH_STATE. lia.
    - rewrite Havo1. lia.
    - exact Hbw1. }
  (* A2: the gzip header *)
  assert (E2 : deflate_body Z_FINISH hs
               = deflate_run Z_FINISH (flush_pending (gzip_header hs))).
  { apply deflate_body_gzheader.
    - exact Hst1.
    - exact Hbw1.
    - exact Hbv1.
    - change (zs_availout (d_strm hs)) with (zs_availout (d_strm s1)).
      rewrite Havo1. lia. }
  assert (Hpin : gzip_header hs
    = setD_status BUSY_STATE
        (setD_ts
           (put_byte OS_CODE (put_byte 2 (put_byte 0 (put_byte 0
              (put_byte 0 (put_byte 0 (put_byte 0 (put_byte 8
                (put_byte 139 (put_byte 31
                  (d_ts (setD_strm (setZ_adler (crc32_z 0 true 0 [])
                                      (d_strm hs)) hs))))))))))))
           (setD_strm (setZ_adler (crc32_z 0 true 0 []) (d_strm hs)) hs))).
  { apply gzip_header_pinned.
    change (d_cfg hs) with (d_cfg s1). rewrite Hcfg1. exact Hlvl. }
  set (zh := setD_status BUSY_STATE
        (setD_ts
           (put_byte OS_CODE (put_byte 2 (put_byte 0 (put_byte 0
              (put_byte 0 (put_byte 0 (put_byte 0 (put_byte 8
                (put_byte 139 (put_byte 31
                  (d_ts (setD_strm (setZ_adler (crc32_z 0 true 0 [])
                                      (d_strm hs)) hs))))))))))))
           (setD_strm (setZ_adler (crc32_z 0 true 0 []) (d_strm hs)) hs))).
  assert (Hbwzh : bw_out (ts_bw (d_ts zh)) = [31; 139; 8; 0; 0; 0; 0; 0; 2; 3])
    by (vm_compute; reflexivity).
  assert (Hbvzh : bw_valid (ts_bw (d_ts zh)) = 0)
    by (vm_compute; reflexivity).
  assert (Hfitzh : zlen (bw_out (ts_bw (d_ts zh))) <= zs_availout (d_strm zh)).
  { rewrite Hbwzh.
    unfold zh. dsimp.
    change (zs_availout (d_strm hs)) with (zs_availout (d_strm s1)).
    rewrite Havo1.
    change (zlen [31; 139; 8; 0; 0; 0; 0; 0; 2; 3]) with 10. lia. }
  destruct (flush_pending_all zh Hbvzh Hfitzh)
    as (Fout & Favo & Fbw & Fbv & Fstat & Fwrap & Fcfg & Fls & Fin
        & Fdn & Fti & Fad & Fsb & Fsn & FtL & FtD).
  rewrite Hbwzh in Fout, Favo.
  assert (Fbuf : bw_buf (ts_bw (d_ts (flush_pending zh)))
                 = bw_buf (ts_bw (d_ts zh))).
  { clear -Hbvzh.
    assert (Hfbw : ts_bw (tr_flush_bits (d_ts zh)) = ts_bw (d_ts zh))
      by (unfold tr_flush_bits; cbn [ts_bw set_bw];
          apply bw_flush_valid0; exact Hbvzh).
    unfold flush_pending. cbv zeta.
    destruct (Z.eqb _ 0); dsimp; cbn [ts_bw set_bw bw_buf];
      rewrite ?Hfbw; reflexivity. }
  set (sd := flush_pending zh) in *.
  assert (Houtsd : zs_out (d_strm sd) = [31; 139; 8; 0; 0; 0; 0; 0; 2; 3])
    by (rewrite Fout; vm_compute; reflexivity).
  assert (Havosd : zs_availout (d_strm sd) = zr_deflate_bound 31 (zlen x) - 10).
  { rewrite Favo.
    change (zlen [31; 139; 8; 0; 0; 0; 0; 0; 2; 3]) with 10.
    vm_compute. reflexivity. }
  assert (Hinsd : zs_in (d_strm sd) = x)
    by (rewrite Fin; vm_compute; reflexivity).
  assert (Hdnsd : zs_done (d_strm sd) = [])
    by (rewrite Fdn; vm_compute; reflexivity).
  assert (Hcfgsd : d_cfg sd = g)
    by (rewrite Fcfg; vm_compute; reflexivity).
  assert (Hwrapsd : d_wrap sd = 2)
    by (rewrite Fwrap; vm_compute; reflexivity).
  assert (Hstatsd : d_status sd = BUSY_STATE)
    by (rewrite Fstat; vm_compute; reflexivity).
  assert (Hlssd : d_ls sd = d_ls (deflate_reset g 2))
    by (rewrite Fls; vm_compute; reflexivity).
  assert (Hbs0 : ls_blockstart (d_ls sd) = 0)
    by (rewrite Hlssd; vm_compute; reflexivity).
  assert (Hbufsd : bw_buf (ts_bw (d_ts sd)) = 0)
    by (rewrite Fbuf; vm_compute; reflexivity).
  (* DsInv at the dispatch state *)
  assert (HI : DsInv g 2 0 (fun _ => False) [] sd).
  { apply (dsinv_init g 15 15 2 x sd Hgeom).
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
      + intros K. discriminate K.
      + intros _. rewrite Fad, Hdnsd. vm_compute. reflexivity.
    - exact Hx. }
  assert (Hmd : dg_max_dist g = 32506).
  { pose proof Eg as Eg2. vm_compute in Eg2.
    injection Eg2 as EgE. rewrite <- EgE. vm_compute. reflexivity. }
  (* the walk *)
  assert (Havosd0 : 0 <= zs_availout (d_strm sd)) by (rewrite Havosd; lia).
  destruct (deflate_slow_finish g 15 15 2 0 (fun _ => False) [] sd
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
  { unfold zh; dsimp; do 10 (apply treeinv_putbyte); exact HTIhs. }
  assert (HTIsd : ZRTreeInv (d_ts sd))
    by (apply treeinv_flush_pending; exact HTIzh).
  assert (Hstatsd2 : ts_optlen (d_ts sd) = 0 /\ ts_statlen (d_ts sd) = 0).
  { apply statzero_flush_pending; unfold zh; dsimp;
    do 10 (apply statzero_putbyte); exact statzero_init. }
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
  assert (Hwst : d_wrap st = 2).
  { change (d_wrap st) with (d_wrap s'). rewrite FwS. exact Hwrapsd. }
  assert (Hbwst : bw_out (ts_bw (d_ts st)) = [])
    by (change (d_ts st) with (d_ts s'); exact Hbw').
  assert (Hbvst : bw_valid (ts_bw (d_ts st)) = 0)
    by (change (d_ts st) with (d_ts s'); exact Hbv').
  assert (Havost : 8 <= zs_availout (d_strm st))
    by (change (d_strm st) with (d_strm s'); exact Havo4).
  pose proof (deflate_trailer_gzip st Hwst Hbwst Hbvst Havost) as HT.
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
  assert (Eout' : zs_out (d_strm s') = [31; 139; 8; 0; 0; 0; 0; 0; 2; 3] ++ body)
    by (rewrite Ebody, Houtsd; reflexivity).
  split; [exact Eout'|].
  split; [rewrite Elenb, Havosd; reflexivity|].
  (* the Some equation *)
  unfold zr_deflate, ZR_STRATEGY, defl_new.
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
  change (zs_totalin (d_strm st)) with (zs_totalin (d_strm s')).
  reflexivity.
Qed.

Print Assumptions emitter_shell_gz.
