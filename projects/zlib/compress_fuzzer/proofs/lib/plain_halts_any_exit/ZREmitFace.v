(** * ZREmitFace — the (default, zlib) emitter face, modulo two seams.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).  G5, part 6.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [emitter_face_modulo] : ZR_BoundSeam -> ZR_ThreadSeam ->
                            ZRepro_Emitter_default_zlib.

    The two seam [Definition]s package the OPEN obligations against the
    exact run pack [ZR_ShellPack] that [ZREmitShell.emitter_shell]
    produces (its conjunction, verbatim):

      * [ZR_BoundSeam] (G6, lane g6-bound): the one deflate(Z_FINISH)
        call at [avail_out = deflateBound] exits [FinishDone] with at
        least the 4 trailer bytes of room — i.e. the emitted stream fits
        the bound.  The pack's [NeedMore]/[FinishStarted] arms carry
        their [avail_out = 0] witness, which is what the size accounting
        refutes; [EvChain] equates emitted bytes with the availout drop.

      * [ZR_ThreadSeam] (walk-threading, this lane, pending an earlier development run's
        R1/R2/R3 re-exports): every flush event satisfies the
        [ZR_SpanGuard] and [ZR_DynEntry] bundles (ZREmitBody).

    Everything else — the header bytes, the frame shape, the body
    decode, the adler trailer, the size bound — is closed here. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  StreamPos CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwStep
  SwDrain SwInit SwSlow G5Chain ZREmitShell ZREmitBody ZREmitBytes
  ZRTreeState ZREvSnap ZRThread Gap7Strict.
Import ListNotations.
Import SymbolIdDeclIface.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(* ==========================================================================
   1.  The run pack — [emitter_shell]'s conjunction, verbatim.
   ========================================================================== *)

Definition ZR_ShellPack (x : list Z) (g : DeflGeom) (sd : DSt)
           (bs : BlockState) (s' : DSt) (evs : list FlushEv) : Prop :=
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

Lemma emitter_shell_pack : forall x,
  Forall (fun b => 0 <= b < 256) x ->
  exists g sd bs s' evs, ZR_ShellPack x g sd bs s' evs.
Proof.
  intros x Hx.
  destruct (emitter_shell x Hx) as (g & sd & bs & s' & evs & P).
  exists g, sd, bs, s', evs. exact P.
Qed.

(* ==========================================================================
   2.  The two seams.
   ========================================================================== *)

(** G6: the emitted stream fits the bound — the walk exits [FinishDone]
    with the 4 trailer bytes of room.  Lane g6-bound's obligation. *)
Definition ZR_BoundSeam : Prop :=
  forall x g sd bs s' evs,
    Forall (fun b => 0 <= b < 256) x ->
    zlen x < ZR_MAX_INPUT ->
    ZR_ShellPack x g sd bs s' evs ->
    bs = FinishDone /\ 4 <= zs_availout (d_strm s').

(** Walk-threading: the tree-state bundles at every flush event.  This
    lane's obligation, pending an earlier development run's R1/R2/R3 re-exports. *)
Definition ZR_ThreadSeam : Prop :=
  forall x g sd bs s' evs,
    Forall (fun b => 0 <= b < 256) x ->
    ZR_ShellPack x g sd bs s' evs ->
    Forall ZR_SpanGuard evs
    /\ Forall (fun e => ZR_DynEntry (d_ts (fe_s e))) evs.

(* ==========================================================================
   3.  Closed arithmetic: the trailer bytes ARE [be32], and the bound is
       at least the fixed overhead.
   ========================================================================== *)

Lemma trailer_bytes_be32 : forall ad,
  [u8 (Z.shiftr (Z.shiftr ad 16) 8);
   u8 (Z.land (Z.shiftr ad 16) 255);
   u8 (Z.shiftr (Z.land ad 65535) 8);
   u8 (Z.land (Z.land ad 65535) 255)] = be32 ad.
Proof.
  intro ad.
  unfold be32, u8.
  change 255 with (Z.ones 8).
  change 65535 with (Z.ones 16).
  rewrite Z.shiftr_shiftr by lia.
  change (16 + 8) with 24.
  rewrite !Z.land_ones by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256.
  change (2 ^ 16) with 65536.
  change (2 ^ 24) with 16777216.
  assert (E : ad mod 65536 = ad + - (ad / 65536) * 256 * 256).
  { pose proof (Z_div_mod_eq_full ad 65536). lia. }
  assert (E2 : ((ad / 65536) mod 256) mod 256 = (ad / 65536) mod 256)
    by (apply Z.mod_mod; lia).
  assert (E3 : ((ad mod 65536) / 256) mod 256 = (ad / 256) mod 256).
  { rewrite E, Z.div_add by lia. rewrite Z_mod_plus_full. reflexivity. }
  assert (E4 : ((ad mod 65536) mod 256) mod 256 = ad mod 256).
  { rewrite Z.mod_mod by lia.
    rewrite E.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite E2, E3, E4.
  reflexivity.
Qed.

Lemma zr_bound_lo : forall n, 0 <= n -> 13 <= zr_deflate_bound 15 n.
Proof.
  intros n Hn.
  unfold zr_deflate_bound.
  change (zr_wraplen 15) with 6.
  pose proof (proj2 (Z.shiftr_nonneg n 12) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 14) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 25) Hn).
  lia.
Qed.

(* ==========================================================================
   4.  The face, modulo the seams.
   ========================================================================== *)

Theorem emitter_face_modulo :
  ZR_BoundSeam -> ZR_ThreadSeam ->
  ZRepro_Emitter_default_zlib.
Proof.
  intros HBS HTS x HIx.
  destruct HIx as (Hx & Hcap).
  destruct (emitter_shell_pack x Hx) as (g & sd & bs & s' & evs & P).
  destruct (HBS x g sd bs s' evs Hx Hcap P) as (Hfd & Havo4).
  destruct (HTS x g sd bs s' evs Hx P) as (HSpan & HDyn).
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HO & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile2 & HTIsd & HTIs' & HTIevs & Hmd).
  destruct (Hcond Hfd Havo4) as (body & Eout' & Elenb & Ezr).
  (* the walk ended in the final-block branch *)
  destruct Hout as [HL | HR].
  2: { destruct HR as (Ebs & _ & _). rewrite Hfd in Ebs. discriminate Ebs. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & HT & Ein' & Edone & HK
                  & Hti & _).
  set (ad := zs_adler (d_strm s')).
  exists ([120; 156] ++ body
          ++ [u8 (Z.shiftr (Z.shiftr ad 16) 8);
              u8 (Z.land (Z.shiftr ad 16) 255);
              u8 (Z.shiftr (Z.land ad 65535) 8);
              u8 (Z.land (Z.land ad 65535) 255)]).
  split; [exact Ezr|].
  split.
  { (* the size bound *)
    rewrite !zlen_app.
    change (zlen [120; 156]) with 2.
    match goal with
    | |- context [zlen [?a; ?b; ?c; ?d]] =>
        change (zlen [a; b; c; d]) with 4
    end.
    pose proof (zr_bound_lo (zlen x) (zlen_nonneg x)).
    lia. }
  split.
  { (* every emitted byte is in range *)
    assert (Hout' : Forall (fun b => 0 <= b < 256) (zs_out (d_strm s'))).
    { destruct (evchain_out_bytes _ _ _ _ _ _ _ HC
                  ltac:(unfold BwBytes; rewrite Hbwsd; constructor)
                  ltac:(rewrite Houtsd; apply Forall_forall;
                        intros v Hv; cbn in Hv;
                        destruct Hv as [<-|[<-|[]]]; lia))
        as (HoutS & _).
      exact HoutS. }
    rewrite Eout' in Hout'.
    apply Forall_app in Hout'. destruct Hout' as (Hhd & Hbody).
    apply Forall_app. split; [exact Hhd|].
    apply Forall_app. split; [exact Hbody|].
    apply Forall_forall. intros v Hv. cbn in Hv.
    destruct Hv as [<-|[<-|[<-|[<-|[]]]]]; apply u8_range. }
  (* the frame *)
  unfold ZR_FramedZlib.
  exists 120, 156, body, ad.
  split.
  { (* ZlibFramed *)
    unfold ZlibFramed.
    rewrite <- (trailer_bytes_be32 ad).
    reflexivity. }
  split.
  { (* ZlibHeaderOk; clause 4 (FDICT clear) is 156&32 = 0 *)
    unfold ZlibHeaderOk.
    split; [reflexivity|].
    split; [change (Z.shiftr (u8 120) 4) with 7; lia|].
    split; reflexivity. }
  split.
  { (* BodyDecodesTo *)
    rewrite Ee in HO, HC, HSpan, HDyn.
    exact (proj1 (body_decodes g 1 x sd s' evs0 evf body [120; 156]
             ltac:(rewrite Hlvl; lia) Hx HO HC
             Houtsd Hbwsd Hbvsd Hbufsd
             ltac:(rewrite Havosd;
                   pose proof (zr_bound_lo (zlen x) (zlen_nonneg x)); lia)
             H0s Hl1 ltac:(rewrite <- Ee; exact HT) Edone Eout'
             ltac:(lia)
             HSpan HDyn)). }
  (* TrailerMatchesPayload *)
  unfold TrailerMatchesPayload, adler_init, ad.
  destruct HK as (HK1 & _).
  rewrite (HK1 eq_refl), Edone.
  reflexivity.
Qed.

Print Assumptions emitter_face_modulo.

(* ==========================================================================
   5.  The ThreadSeam, reduced to its two named residuals.

   The pack now carries [ZRTreeInv] at every flush snapshot
   (walk-threaded), so [ZR_DynEntry] follows per event by
   [ZRThread.treeinv_dynentry] modulo:
     * [ZR_BlfAll]  — the all-indices BL-freshness spelling of the landed
       dyn-arm keystones (REPAIR-PENDING: the reachable states only
       satisfy the in-range form; weakening relayed to an earlier development run), and
     * [ZR_MaxcD]   — the forced distance-tree maxcode lower bound
       (bt_force2 analysis, own derivation pending),
   plus the stored-arm span guard.
   ========================================================================== *)

Definition ZR_SpanSeam : Prop :=
  forall x g sd bs s' evs,
    Forall (fun b => 0 <= b < 256) x ->
    ZR_ShellPack x g sd bs s' evs ->
    Forall ZR_SpanGuard evs.

Definition ZR_StaleSeam : Prop :=
  forall x g sd bs s' evs,
    Forall (fun b => 0 <= b < 256) x ->
    ZR_ShellPack x g sd bs s' evs ->
    Forall (fun ev => ZR_BlfAll (d_ts (fe_s ev))) evs.

Theorem threadseam_from_residuals :
  ZR_SpanSeam -> ZR_StaleSeam -> ZR_ThreadSeam.
Proof.
  intros HS HR x g sd bs s' evs Hx P.
  split; [exact (HS x g sd bs s' evs Hx P)|].
  pose proof (HR x g sd bs s' evs Hx P) as HRes.
  assert (HTIevs : Forall (fun ev => ZRTreeInv (d_ts (fe_s ev))) evs).
  { destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & _).
    eapply Forall_impl; [|exact HT].
    intros ev0 HE. exact (proj1 HE). }
  clear P.
  induction evs as [|ev evs IH]; [constructor|].
  inversion HRes as [|? ? HRh HRt]; subst.
  inversion HTIevs as [|? ? HTh HTt]; subst.
  constructor.
  - apply treeinv_dynentry; [exact HTh | exact HRh | apply maxcd_all].
  - apply IH; [exact HRt | exact HTt].
Qed.

Theorem emitter_face_modulo3 :
  ZR_BoundSeam -> ZR_SpanSeam -> ZR_StaleSeam ->
  ZRepro_Emitter_default_zlib.
Proof.
  intros HB HS HR.
  apply emitter_face_modulo; [exact HB|].
  apply threadseam_from_residuals; [exact HS | exact HR].
Qed.

Print Assumptions emitter_face_modulo3.

(* ==========================================================================
   6.  q7 F4: the body slice is consumed to within ONE byte.

   [ZR_FramedZlib] (frozen in ZRepro.v) carries the remainder-DISCARDING
   [BodyDecodesTo]; the pump's tail reads need the leftover bounded.  The
   Z_FINISH windup pads by [bw_pad] (< 8 bits) and nothing follows it, so
   the decode leftover of the body slice is exactly that pad —
   [IsValidStreamFor] (DeflateSpec §11).  Same run, same seams; a SIBLING
   theorem because the frozen frame cannot carry the extra conjunct.
   ========================================================================== *)

Definition ZR_BodyValidZlib : Prop :=
  forall x, ZR_Input x ->
    exists enc b0 b1 body ad,
      zr_deflate ZR_DEFAULT_LEVEL 15 x = Some enc
      /\ ZlibFramed enc b0 b1 body ad
      /\ Forall (fun b => 0 <= b < 256) body
      /\ IsValidStreamFor body x.

Theorem bodyvalid_modulo :
  ZR_BoundSeam -> ZR_ThreadSeam ->
  ZR_BodyValidZlib.
Proof.
  intros HBS HTS x HIx.
  destruct HIx as (Hx & Hcap).
  destruct (emitter_shell_pack x Hx) as (g & sd & bs & s' & evs & P).
  destruct (HBS x g sd bs s' evs Hx Hcap P) as (Hfd & Havo4).
  destruct (HTS x g sd bs s' evs Hx P) as (HSpan & HDyn).
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HO & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile2 & HTIsd & HTIs' & HTIevs & Hmd).
  destruct (Hcond Hfd Havo4) as (body & Eout' & Elenb & Ezr).
  destruct Hout as [HL | HR].
  2:{ destruct HR as (Ebs & _ & _). rewrite Hfd in Ebs. discriminate Ebs. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & HT & Ein' & Edone & HK
                  & Hti & _).
  set (ad := zs_adler (d_strm s')).
  exists ([120; 156] ++ body
          ++ [u8 (Z.shiftr (Z.shiftr ad 16) 8);
              u8 (Z.land (Z.shiftr ad 16) 255);
              u8 (Z.shiftr (Z.land ad 65535) 8);
              u8 (Z.land (Z.land ad 65535) 255)]),
         120, 156, body, ad.
  split; [exact Ezr|].
  split.
  { unfold ZlibFramed.
    rewrite <- (trailer_bytes_be32 ad).
    reflexivity. }
  split.
  { (* the body bytes are in range, from the chain *)
    assert (Hout' : Forall (fun b => 0 <= b < 256) (zs_out (d_strm s'))).
    { destruct (evchain_out_bytes _ _ _ _ _ _ _ HC
                  ltac:(unfold BwBytes; rewrite Hbwsd; constructor)
                  ltac:(rewrite Houtsd; apply Forall_forall;
                        intros v Hv; cbn in Hv;
                        destruct Hv as [<-|[<-|[]]]; lia))
        as (HoutS & _).
      exact HoutS. }
    rewrite Eout' in Hout'.
    apply Forall_app in Hout'. destruct Hout' as (_ & Hbody).
    exact Hbody. }
  rewrite Ee in HO, HC, HSpan, HDyn.
  exact (proj1 (proj2 (body_decodes g 1 x sd s' evs0 evf body [120; 156]
           ltac:(rewrite Hlvl; lia) Hx HO HC
           Houtsd Hbwsd Hbvsd Hbufsd
           ltac:(rewrite Havosd;
                 pose proof (zr_bound_lo (zlen x) (zlen_nonneg x)); lia)
           H0s Hl1 ltac:(rewrite <- Ee; exact HT) Edone Eout'
           ltac:(lia)
           HSpan HDyn))).
Qed.

Theorem bodyvalid_modulo3 :
  ZR_BoundSeam -> ZR_SpanSeam -> ZR_StaleSeam ->
  ZR_BodyValidZlib.
Proof.
  intros HB HS HR.
  apply bodyvalid_modulo; [exact HB|].
  apply threadseam_from_residuals; [exact HS | exact HR].
Qed.

Print Assumptions bodyvalid_modulo3.

(* ==========================================================================
   7.  GAP7 strict decode: the body slice passes the MACHINE-accept
   guards at every dynamic header, modulo the two frozen statements
   (g1's characterization bridge + the ENOUGH residue).
   ========================================================================== *)

Definition ZR_BodyStrictZlib : Prop :=
  forall x, ZR_Input x ->
    exists enc b0 b1 body ad,
      zr_deflate ZR_DEFAULT_LEVEL 15 x = Some enc
      /\ ZlibFramed enc b0 b1 body ad
      /\ Forall (fun b => 0 <= b < 256) body
      /\ (exists rem, dec_stream_from_strict (bytes_bits body) []
                      = Some (x, rem)
                   /\ (length rem < 8)%nat).

Theorem bodystrict_modulo :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
  ZR_BoundSeam -> ZR_ThreadSeam ->
  ZR_BodyStrictZlib.
Proof.
  intros HBK EFR HBS HTS x HIx.
  destruct HIx as (Hx & Hcap).
  destruct (emitter_shell_pack x Hx) as (g & sd & bs & s' & evs & P).
  destruct (HBS x g sd bs s' evs Hx Hcap P) as (Hfd & Havo4).
  destruct (HTS x g sd bs s' evs Hx P) as (HSpan & HDyn).
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HO & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile2 & HTIsd & HTIs' & HTIevs & Hmd).
  destruct (Hcond Hfd Havo4) as (body & Eout' & Elenb & Ezr).
  destruct Hout as [HL | HR].
  2:{ destruct HR as (Ebs & _ & _). rewrite Hfd in Ebs. discriminate Ebs. }
  destruct HL as (evs0 & evf & Ee & H0s & Hl1 & HT & Ein' & Edone & HK
                  & Hti & _).
  set (ad := zs_adler (d_strm s')).
  exists ([120; 156] ++ body
          ++ [u8 (Z.shiftr (Z.shiftr ad 16) 8);
              u8 (Z.land (Z.shiftr ad 16) 255);
              u8 (Z.shiftr (Z.land ad 65535) 8);
              u8 (Z.land (Z.land ad 65535) 255)]),
         120, 156, body, ad.
  split; [exact Ezr|].
  split.
  { unfold ZlibFramed.
    rewrite <- (trailer_bytes_be32 ad).
    reflexivity. }
  split.
  { (* the body bytes are in range, from the chain *)
    assert (Hout' : Forall (fun b => 0 <= b < 256) (zs_out (d_strm s'))).
    { destruct (evchain_out_bytes _ _ _ _ _ _ _ HC
                  ltac:(unfold BwBytes; rewrite Hbwsd; constructor)
                  ltac:(rewrite Houtsd; apply Forall_forall;
                        intros v Hv; cbn in Hv;
                        destruct Hv as [<-|[<-|[]]]; lia))
        as (HoutS & _).
      exact HoutS. }
    rewrite Eout' in Hout'.
    apply Forall_app in Hout'. destruct Hout' as (_ & Hbody).
    exact Hbody. }
  rewrite Ee in HO, HC, HSpan, HDyn.
  exact (proj2 (proj2 (body_decodes g 1 x sd s' evs0 evf body [120; 156]
           ltac:(rewrite Hlvl; lia) Hx HO HC
           Houtsd Hbwsd Hbvsd Hbufsd
           ltac:(rewrite Havosd;
                 pose proof (zr_bound_lo (zlen x) (zlen_nonneg x)); lia)
           H0s Hl1 ltac:(rewrite <- Ee; exact HT) Edone Eout'
           ltac:(lia)
           HSpan HDyn)) HBK EFR).
Qed.

Theorem bodystrict_modulo3 :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
  ZR_BoundSeam -> ZR_SpanSeam -> ZR_StaleSeam ->
  ZR_BodyStrictZlib.
Proof.
  intros HBK EFR HB HS HR.
  apply (bodystrict_modulo HBK EFR); [exact HB|].
  apply threadseam_from_residuals; [exact HS | exact HR].
Qed.

Print Assumptions bodystrict_modulo3.
