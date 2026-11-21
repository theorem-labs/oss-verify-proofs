(** * ZRGzFace — the level-9 gzip emitter face, modulo three seams.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [emitter_face_gz_modulo3] : ZR_GzBoundSeam -> ZR_GzSpanSeam ->
    ZR_GzStaleSeam -> ZRepro_Emitter_l9_gzip.

    The seams mirror the default-zlib face's (ZREmitFace): the bound
    (FinishDone with 8 trailer bytes of room), the stored-arm span guard,
    and the repair-pending all-indices BL-freshness residual.  Header
    bytes, the frame equality (CRC32 via [CkInv]'s wrap-2 clause — the
    [crc32_z_at]/[crc32_z false] bridge is definitional — and ISIZE via
    the exported [total_in]), byte-range, the size bound and the body
    decode are closed here. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  StreamPos CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwStep
  SwDrain SwInit SwSlow G5Chain ZREmitShell ZREmitBody ZREmitBytes
  ZRTreeState ZREvSnap ZRThread ZREmitGz ZRGzShell ZREmitFace Gap7Strict.
Import ListNotations.
Import SymbolIdDeclIface.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(* ==========================================================================
   1.  The run pack — [emitter_shell_gz]'s conjunction, verbatim.
   ========================================================================== *)

Definition ZR_GzPack (x : list Z) (g : DeflGeom) (sd : DSt)
           (bs : BlockState) (s' : DSt) (evs : list FlushEv) : Prop :=

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

Lemma emitter_shell_gz_pack : forall x,
  Forall (fun b => 0 <= b < 256) x ->
  exists g sd bs s' evs, ZR_GzPack x g sd bs s' evs.
Proof.
  intros x Hx.
  destruct (emitter_shell_gz x Hx) as (g & sd & bs & s' & evs & P).
  exists g, sd, bs, s', evs. exact P.
Qed.

(* ==========================================================================
   2.  The three seams.
   ========================================================================== *)

Definition ZR_GzBoundSeam : Prop :=
  forall x g sd bs s' evs,
    Forall (fun b => 0 <= b < 256) x ->
    zlen x < ZR_MAX_INPUT ->
    ZR_GzPack x g sd bs s' evs ->
    bs = FinishDone /\ 8 <= zs_availout (d_strm s').

Definition ZR_GzSpanSeam : Prop :=
  forall x g sd bs s' evs,
    Forall (fun b => 0 <= b < 256) x ->
    ZR_GzPack x g sd bs s' evs ->
    Forall ZR_SpanGuard evs.

Definition ZR_GzStaleSeam : Prop :=
  forall x g sd bs s' evs,
    Forall (fun b => 0 <= b < 256) x ->
    ZR_GzPack x g sd bs s' evs ->
    Forall (fun ev => ZR_BlfAll (d_ts (fe_s ev))) evs.

(* ==========================================================================
   3.  Closed byte arithmetic.
   ========================================================================== *)

Lemma u8_land : forall v, u8 v = Z.land v 255.
Proof.
  intro v. unfold u8.
  change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia.
  reflexivity.
Qed.

Lemma le32_of_u8 : forall v,
  [u8 v; u8 (Z.shiftr v 8); u8 (Z.shiftr v 16); u8 (Z.shiftr v 24)]
  = zr_le32 v.
Proof.
  intro v. unfold zr_le32.
  rewrite !u8_land. reflexivity.
Qed.

Lemma zr_bound_lo_gz : forall n, 0 <= n -> 25 <= zr_deflate_bound 31 n.
Proof.
  intros n Hn.
  unfold zr_deflate_bound.
  change (zr_wraplen 31) with 18.
  pose proof (proj2 (Z.shiftr_nonneg n 12) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 14) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 25) Hn).
  lia.
Qed.

(* ==========================================================================
   4.  The face, modulo the seams.
   ========================================================================== *)

Theorem emitter_face_gz_modulo3 :
  ZR_GzBoundSeam -> ZR_GzSpanSeam -> ZR_GzStaleSeam ->
  ZRepro_Emitter_l9_gzip.
Proof.
  intros HBS HSS HRS x HIx.
  destruct HIx as (Hx & Hcap).
  destruct (emitter_shell_gz_pack x Hx) as (g & sd & bs & s' & evs & P).
  destruct (HBS x g sd bs s' evs Hx Hcap P) as (Hfd & Havo8).
  pose proof (HSS x g sd bs s' evs Hx P) as HSpan.
  pose proof (HRS x g sd bs s' evs Hx P) as HStale.
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HO & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile2 & HTIsd & HTIs' & HTIevs & Hmd).
  assert (HTIevs2 : Forall (fun ev => ZRTreeInv (d_ts (fe_s ev))) evs).
  { eapply Forall_impl; [|exact HTIevs]. intros ev0 HE. exact (proj1 HE). }
  pose proof (dynentries_from_invariants evs HTIevs2 HStale) as HDyn.
  destruct (Hcond Hfd Havo8) as (body & Eout' & Elenb & Ezr).
  destruct Hout as [HL | HR].
  2:{ destruct HR as (Ebs & _ & _). rewrite Hfd in Ebs. discriminate Ebs. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & HT & Ein' & Edone & HK
                  & Hti & _).
  set (ad := zs_adler (d_strm s')).
  set (ti := zs_totalin (d_strm s')).
  exists ([31; 139; 8; 0; 0; 0; 0; 0; 2; 3] ++ body
          ++ [u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
              u8 (Z.shiftr ad 24);
              u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
              u8 (Z.shiftr ti 24)]).
  split; [exact Ezr|].
  split.
  { (* the size bound *)
    rewrite !zlen_app.
    change (zlen [31; 139; 8; 0; 0; 0; 0; 0; 2; 3]) with 10.
    match goal with
    | |- context [zlen [?a; ?b; ?c; ?d; ?e; ?f; ?g0; ?h]] =>
        change (zlen [a; b; c; d; e; f; g0; h]) with 8
    end.
    pose proof (zr_bound_lo_gz (zlen x) (zlen_nonneg x)).
    lia. }
  split.
  { (* every emitted byte is in range *)
    assert (Hout' : Forall (fun b => 0 <= b < 256) (zs_out (d_strm s'))).
    { destruct (evchain_out_bytes _ _ _ _ _ _ _ HC
                  ltac:(unfold BwBytes; rewrite Hbwsd; constructor)
                  ltac:(rewrite Houtsd; apply Forall_forall;
                        intros v Hv; cbn in Hv; intuition lia))
        as (HoutS & _).
      exact HoutS. }
    rewrite Eout' in Hout'.
    apply Forall_app in Hout'. destruct Hout' as (Hhd & Hbody).
    apply Forall_app. split; [exact Hhd|].
    apply Forall_app. split; [exact Hbody|].
    apply Forall_forall. intros v Hv. cbn in Hv.
    destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
      apply u8_range. }
  (* the frame *)
  unfold ZR_FramedGzip.
  exists body.
  split.
  { (* the byte-level equality *)
    assert (Had : ad = crc32_z zr_crc_init false 0 x).
    { destruct HK as (_ & HK2).
      unfold ad. rewrite (HK2 eq_refl), Edone.
      reflexivity. }
    assert (Hti' : ti = zlen x)
      by (unfold ti; rewrite Hti; reflexivity).
    change (zr_gzip_header 9) with [31; 139; 8; 0; 0; 0; 0; 0; 2; 3].
    f_equal. f_equal.
    change ([u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
             u8 (Z.shiftr ad 24);
             u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
             u8 (Z.shiftr ti 24)])
      with ([u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
             u8 (Z.shiftr ad 24)]
            ++ [u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
                u8 (Z.shiftr ti 24)]).
    rewrite !le32_of_u8.
    rewrite Had, Hti'.
    reflexivity. }
  (* BodyDecodesTo *)
  rewrite Ee in HO, HC, HSpan, HDyn.
  exact (proj1 (body_decodes g 2 x sd s' evs0 evf body
           [31; 139; 8; 0; 0; 0; 0; 0; 2; 3]
           ltac:(rewrite Hlvl; lia) Hx HO HC
           Houtsd Hbwsd Hbvsd Hbufsd
           ltac:(rewrite Havosd;
                 pose proof (zr_bound_lo_gz (zlen x) (zlen_nonneg x)); lia)
           H0s Hl1 ltac:(rewrite <- Ee; exact HT) Edone Eout'
           ltac:(lia)
           HSpan HDyn)).
Qed.

Print Assumptions emitter_face_gz_modulo3.

(* ==========================================================================
   5.  q7 F4: the gzip body slice is consumed to within ONE byte.
   Twin of ZREmitFace.ZR_BodyValidZlib — see the rationale there.
   ========================================================================== *)

Definition ZR_BodyValidGzip : Prop :=
  forall x, ZR_Input x ->
    exists enc body,
      zr_deflate 9 31 x = Some enc
      /\ enc = zr_gzip_header 9 ++ body
               ++ zr_le32 (crc32_z zr_crc_init false 0 x)
               ++ zr_le32 (zlen x)
      /\ Forall (fun b => 0 <= b < 256) body
      /\ IsValidStreamFor body x.

Theorem gz_bodyvalid_modulo3 :
  ZR_GzBoundSeam -> ZR_GzSpanSeam -> ZR_GzStaleSeam ->
  ZR_BodyValidGzip.
Proof.
  intros HBS HSS HRS x HIx.
  destruct HIx as (Hx & Hcap).
  destruct (emitter_shell_gz_pack x Hx) as (g & sd & bs & s' & evs & P).
  destruct (HBS x g sd bs s' evs Hx Hcap P) as (Hfd & Havo8).
  pose proof (HSS x g sd bs s' evs Hx P) as HSpan.
  pose proof (HRS x g sd bs s' evs Hx P) as HStale.
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HO & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile2 & HTIsd & HTIs' & HTIevs & Hmd).
  assert (HTIevs2 : Forall (fun ev => ZRTreeInv (d_ts (fe_s ev))) evs).
  { eapply Forall_impl; [|exact HTIevs]. intros ev0 HE. exact (proj1 HE). }
  pose proof (dynentries_from_invariants evs HTIevs2 HStale) as HDyn.
  destruct (Hcond Hfd Havo8) as (body & Eout' & Elenb & Ezr).
  destruct Hout as [HL | HR].
  2:{ destruct HR as (Ebs & _ & _). rewrite Hfd in Ebs. discriminate Ebs. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & HT & Ein' & Edone & HK
                  & Hti & _).
  set (ad := zs_adler (d_strm s')).
  set (ti := zs_totalin (d_strm s')).
  assert (Had : ad = crc32_z zr_crc_init false 0 x).
  { destruct HK as (_ & HK2).
    unfold ad. rewrite (HK2 eq_refl), Edone.
    reflexivity. }
  assert (Hti' : ti = zlen x)
    by (unfold ti; rewrite Hti; reflexivity).
  exists ([31; 139; 8; 0; 0; 0; 0; 0; 2; 3] ++ body
          ++ [u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
              u8 (Z.shiftr ad 24);
              u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
              u8 (Z.shiftr ti 24)]),
         body.
  split; [exact Ezr|].
  split.
  { change (zr_gzip_header 9) with [31; 139; 8; 0; 0; 0; 0; 0; 2; 3].
    f_equal. f_equal.
    change ([u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
             u8 (Z.shiftr ad 24);
             u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
             u8 (Z.shiftr ti 24)])
      with ([u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
             u8 (Z.shiftr ad 24)]
            ++ [u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
                u8 (Z.shiftr ti 24)]).
    rewrite !le32_of_u8.
    rewrite Had, Hti'.
    reflexivity. }
  split.
  { (* the body bytes are in range, from the chain *)
    assert (Hout' : Forall (fun b => 0 <= b < 256) (zs_out (d_strm s'))).
    { destruct (evchain_out_bytes _ _ _ _ _ _ _ HC
                  ltac:(unfold BwBytes; rewrite Hbwsd; constructor)
                  ltac:(rewrite Houtsd; apply Forall_forall;
                        intros v Hv; cbn in Hv; intuition lia))
        as (HoutS & _).
      exact HoutS. }
    rewrite Eout' in Hout'.
    apply Forall_app in Hout'. destruct Hout' as (_ & Hbody).
    exact Hbody. }
  rewrite Ee in HO, HC, HSpan, HDyn.
  exact (proj1 (proj2 (body_decodes g 2 x sd s' evs0 evf body
           [31; 139; 8; 0; 0; 0; 0; 0; 2; 3]
           ltac:(rewrite Hlvl; lia) Hx HO HC
           Houtsd Hbwsd Hbvsd Hbufsd
           ltac:(rewrite Havosd;
                 pose proof (zr_bound_lo_gz (zlen x) (zlen_nonneg x)); lia)
           H0s Hl1 ltac:(rewrite <- Ee; exact HT) Edone Eout'
           ltac:(lia)
           HSpan HDyn))).
Qed.

Print Assumptions gz_bodyvalid_modulo3.

(* ==========================================================================
   6.  GAP7 strict decode, gzip twin — see ZREmitFace's rationale.
   ========================================================================== *)

Definition ZR_BodyStrictGzip : Prop :=
  forall x, ZR_Input x ->
    exists enc body,
      zr_deflate 9 31 x = Some enc
      /\ enc = zr_gzip_header 9 ++ body
               ++ zr_le32 (crc32_z zr_crc_init false 0 x)
               ++ zr_le32 (zlen x)
      /\ Forall (fun b => 0 <= b < 256) body
      /\ (exists rem, dec_stream_from_strict (bytes_bits body) []
                      = Some (x, rem)
                   /\ (length rem < 8)%nat).

Theorem gz_bodystrict_modulo3 :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
  ZR_GzBoundSeam -> ZR_GzSpanSeam -> ZR_GzStaleSeam ->
  ZR_BodyStrictGzip.
Proof.
  intros HBK EFR HBS HSS HRS x HIx.
  destruct HIx as (Hx & Hcap).
  destruct (emitter_shell_gz_pack x Hx) as (g & sd & bs & s' & evs & P).
  destruct (HBS x g sd bs s' evs Hx Hcap P) as (Hfd & Havo8).
  pose proof (HSS x g sd bs s' evs Hx P) as HSpan.
  pose proof (HRS x g sd bs s' evs Hx P) as HStale.
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HO & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile2 & HTIsd & HTIs' & HTIevs & Hmd).
  assert (HTIevs2 : Forall (fun ev => ZRTreeInv (d_ts (fe_s ev))) evs).
  { eapply Forall_impl; [|exact HTIevs]. intros ev0 HE. exact (proj1 HE). }
  pose proof (dynentries_from_invariants evs HTIevs2 HStale) as HDyn.
  destruct (Hcond Hfd Havo8) as (body & Eout' & Elenb & Ezr).
  destruct Hout as [HL | HR].
  2:{ destruct HR as (Ebs & _ & _). rewrite Hfd in Ebs. discriminate Ebs. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & HT & Ein' & Edone & HK
                  & Hti & _).
  set (ad := zs_adler (d_strm s')).
  set (ti := zs_totalin (d_strm s')).
  assert (Had : ad = crc32_z zr_crc_init false 0 x).
  { destruct HK as (_ & HK2).
    unfold ad. rewrite (HK2 eq_refl), Edone.
    reflexivity. }
  assert (Hti' : ti = zlen x)
    by (unfold ti; rewrite Hti; reflexivity).
  exists ([31; 139; 8; 0; 0; 0; 0; 0; 2; 3] ++ body
          ++ [u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
              u8 (Z.shiftr ad 24);
              u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
              u8 (Z.shiftr ti 24)]),
         body.
  split; [exact Ezr|].
  split.
  { change (zr_gzip_header 9) with [31; 139; 8; 0; 0; 0; 0; 0; 2; 3].
    f_equal. f_equal.
    change ([u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
             u8 (Z.shiftr ad 24);
             u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
             u8 (Z.shiftr ti 24)])
      with ([u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
             u8 (Z.shiftr ad 24)]
            ++ [u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
                u8 (Z.shiftr ti 24)]).
    rewrite !le32_of_u8.
    rewrite Had, Hti'.
    reflexivity. }
  split.
  { (* the body bytes are in range, from the chain *)
    assert (Hout' : Forall (fun b => 0 <= b < 256) (zs_out (d_strm s'))).
    { destruct (evchain_out_bytes _ _ _ _ _ _ _ HC
                  ltac:(unfold BwBytes; rewrite Hbwsd; constructor)
                  ltac:(rewrite Houtsd; apply Forall_forall;
                        intros v Hv; cbn in Hv; intuition lia))
        as (HoutS & _).
      exact HoutS. }
    rewrite Eout' in Hout'.
    apply Forall_app in Hout'. destruct Hout' as (_ & Hbody).
    exact Hbody. }
  rewrite Ee in HO, HC, HSpan, HDyn.
  exact (proj2 (proj2 (body_decodes g 2 x sd s' evs0 evf body
           [31; 139; 8; 0; 0; 0; 0; 0; 2; 3]
           ltac:(rewrite Hlvl; lia) Hx HO HC
           Houtsd Hbwsd Hbvsd Hbufsd
           ltac:(rewrite Havosd;
                 pose proof (zr_bound_lo_gz (zlen x) (zlen_nonneg x)); lia)
           H0s Hl1 ltac:(rewrite <- Ee; exact HT) Edone Eout'
           ltac:(lia)
           HSpan HDyn)) HBK EFR).
Qed.

Print Assumptions gz_bodystrict_modulo3.
