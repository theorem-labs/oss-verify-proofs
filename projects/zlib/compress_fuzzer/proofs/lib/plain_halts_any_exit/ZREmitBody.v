(** * ZREmitBody — the decode side of the (default, zlib) emitter face.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).  G5, part 5.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    From ZREmitShell's walk pack to [BodyDecodesTo body x]: each flush
    event becomes a [G5Body.EvBits]/[EvBitsFin] wire pack via
    [G3Event.flush_block_only_bits] (the dynamic arm supplied by
    [G3DynB.dyn_arm_dec_blk]), the packs fold through [G5Body.dec_blocks],
    and the stream arithmetic ties [concat deltas = bytes_bits body].

    TWO INTERIM PREMISE BUNDLES ride as [Forall]s over the events, to be
    discharged when the DsInv walk-threading lands and the size accounting
    (G6, lane g6-bound):
      * [ZR_DynEntry] — the tree-state facts [dyn_arm_dec_blk] consumes
        (entry blcount/BL-freq/BL-len facts + the R1/R2/R3-shaped facts
        at the build outputs), verbatim spellings;
      * [ZR_SpanGuard] — the guard-conditional stored-arm span bound
        (G3Block's [opt_lenb] test), verbatim from
        [flush_block_only_bits]'s premise.
    The [4 <= avail_out] premise is the same G6 seam as the shell's. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  StreamPos CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwStep SwDrain
  G3DynA G3DynB G3Event G5Body ZREmitShell Gap7Strict ZRStrictSupply.
Import ListNotations.
Import SymbolIdDeclIface.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(* ==========================================================================
   1.  The interim premise bundles, spelled verbatim at their consumers.
   ========================================================================== *)

(** [dyn_arm_dec_blk]'s tree-state premises at one flush snapshot: the
    three walk-threaded entry facts, then the seven facts at the
    [build_tree]/[build_bl_tree] outputs (the R1/R2/R3 family). *)
Definition ZR_DynEntry (ts0 : TSt) : Prop :=
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts0 b = 0)
  /\ (forall i, 0 <= i < 19 -> t_freq (ts_trees ts0 TK_BL) i = 0)
  /\ (forall i, 0 <= t_len (ts_trees ts0 TK_BL) i)
  /\ (forall b, b < 0 \/ 15 < b -> ts_blcount (build_tree TK_L ts0) b = 0)
  /\ (forall i, 0 <= t_len (ts_trees (build_tree TK_L ts0) TK_L) i)
  /\ (forall b, b < 0 \/ 15 < b ->
      ts_blcount (build_tree TK_D (build_tree TK_L ts0)) b = 0)
  /\ (forall i, 0 <= t_len
       (ts_trees (build_tree TK_D (build_tree TK_L ts0)) TK_D) i)
  /\ 1 <= ts_maxcode (build_tree TK_D (build_tree TK_L ts0)) TK_D
  /\ (forall b, b < 0 \/ 15 < b ->
      ts_blcount
        (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0)))) b = 0)
  /\ (forall i, 0 <= t_len
       (ts_trees
          (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0))))
          TK_BL) i).

(** The stored-arm span bound, guard-conditional — verbatim
    [flush_block_only_bits] premise. *)
Definition ZR_SpanGuard (ev : FlushEv) : Prop :=
  0 <= ls_blockstart (d_ls (fe_s ev)) ->
  Z.leb (ls_strstart (d_ls (fe_s ev)) - ls_blockstart (d_ls (fe_s ev)) + 4)
    (if (Z.leb (u64 (ts_statlen (snd (build_bl_tree (build_tree TK_D
                  (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8)
           (u64 (ts_optlen (snd (build_bl_tree (build_tree TK_D
                  (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8))
        || (Z.eqb (dg_strategy (d_cfg (fe_s ev))) Z_FIXED)
     then u64 (ts_statlen (snd (build_bl_tree (build_tree TK_D
            (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8
     else u64 (ts_optlen (snd (build_bl_tree (build_tree TK_D
            (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8)
    = true ->
  fe_end ev - fe_start ev < 65536.

(* ==========================================================================
   2.  One event -> one wire pack.
   ========================================================================== *)

Lemma event_bits : forall g wrap done ev,
  0 < dg_level g ->
  EvOk g wrap done ev ->
  ZR_SpanGuard ev ->
  ZR_DynEntry (d_ts (fe_s ev)) ->
  Forall (fun b => 0 <= b < 256) done ->
  bw_wf (ts_bw (d_ts (fe_s ev))) ->
  exists delta,
    dst_stream (flush_block_only (fe_last ev) (fe_s ev))
      = dst_stream (fe_s ev) ++ delta
    /\ bw_wf (ts_bw (d_ts (flush_block_only (fe_last ev) (fe_s ev))))
    /\ (fe_last ev = 0 -> EvBits done ev delta)
    /\ (fe_last ev = 1 ->
        EvBitsFin done ev delta
        /\ (length (dst_stream (flush_block_only (fe_last ev) (fe_s ev)))
            mod 8 = 0)%nat).
Proof.
  intros g wrap done ev Hlvl HE Hspan Hdyn Hbytes Hwf.
  pose proof HE as HE'.
  destruct HE' as (Ecfg & Ewrap & Hbuf & Hfrq & Henc & Hsn & Hrange & Hendle
                   & Hres & Hspaneq & Hwin & Hl01).
  destruct Hdyn as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  assert (Hdynhyp : forall mbi s2,
      (mbi, s2) = build_bl_tree (build_tree TK_D
                     (build_tree TK_L (d_ts (fe_s ev)))) ->
      exists delta,
        bw_stream (dyn_bw (fe_last ev) mbi s2)
          = bw_stream (ts_bw (d_ts (fe_s ev))) ++ delta
        /\ bw_wf (dyn_bw (fe_last ev) mbi s2)
        /\ (forall suffix,
             dec_blk (delta ++ suffix)
               (firstn (Z.to_nat (fe_start ev)) done)
             = Some (Z.eqb (fe_last ev) 1,
                     firstn (Z.to_nat (fe_end ev)) done, suffix))
        /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
            forall suffix,
             dec_blk_strict (delta ++ suffix)
               (firstn (Z.to_nat (fe_start ev)) done)
             = Some (Z.eqb (fe_last ev) 1,
                     firstn (Z.to_nat (fe_end ev)) done, suffix))).
  { intros mbi s2 Epair.
    assert (Es2 : s2 = snd (build_bl_tree (build_tree TK_D
                             (build_tree TK_L (d_ts (fe_s ev))))))
      by (rewrite <- Epair; reflexivity).
    apply (dyn_arm_dec_blk (d_ts (fe_s ev)) (fe_toks ev) (fe_last ev)
             (firstn (Z.to_nat (fe_start ev)) done)
             (firstn (Z.to_nat (fe_end ev)) done) mbi s2
             Epair Hwf ltac:(lia) Hbuf Hfrq Henc Hres
             D1 D2 D3 D4 D5 D6 D7 D8
             ltac:(rewrite Es2; exact D9)
             ltac:(rewrite Es2; exact D10)). }
  destruct (flush_block_only_bits g wrap done ev HE
              ltac:(exact Hlvl)
              Hspan Hbytes Hwf Hdynhyp)
    as (delta & Hdst & Hwf' & Harm).
  exists delta.
  split; [exact Hdst|].
  split; [exact Hwf'|].
  split.
  - intro H0.
    destruct Harm as [A1 | [A2 | A3]].
    + split; [exact Hdst|]. left. exact A1.
    + split; [exact Hdst|]. right. exact A2.
    + destruct A3 as (E1 & _). rewrite H0 in E1. discriminate E1.
  - intro H1.
    destruct Harm as [A1 | [A2 | A3]].
    + destruct A1 as (E0 & _). rewrite H1 in E0. discriminate E0.
    + destruct A2 as (E0 & _). rewrite H1 in E0. discriminate E0.
    + destruct A3 as (_ & Hmod & Hdec).
      split; [|exact Hmod].
      split; [exact Hdst|].
      split; [exact H1|].
      exact Hdec.
Qed.

(* ==========================================================================
   3.  The chain fold: 0-final events to [Forall2 EvBits], wf threaded.
   ========================================================================== *)

Lemma chain_bits : forall g wrap done evs bw out avo bw' out' avo',
  0 < dg_level g ->
  Forall (EvOk g wrap done) evs ->
  Forall (fun e => fe_last e = 0) evs ->
  Forall ZR_SpanGuard evs ->
  Forall (fun e => ZR_DynEntry (d_ts (fe_s e))) evs ->
  Forall (fun b => 0 <= b < 256) done ->
  EvChain evs bw out avo bw' out' avo' ->
  bw_wf bw ->
  exists deltas,
    Forall2 (EvBits done) evs deltas
    /\ bw_wf bw'.
Proof.
  intros g wrap done evs; induction evs as [|ev evs IH];
    intros bw out avo bw' out' avo' Hlvl HO H0 HS HD Hbytes HC Hwf.
  - cbn [EvChain] in HC. destruct HC as (-> & _ & _).
    exists []. split; [constructor | exact Hwf].
  - cbn [EvChain] in HC.
    destruct HC as (Hb & Ho & Ha & HC).
    destruct (event_bits g wrap done ev Hlvl
                (Forall_inv HO) (Forall_inv HS) (Forall_inv HD) Hbytes
                ltac:(rewrite Hb; exact Hwf))
      as (delta & Hdst & Hwf' & HB0 & _).
    destruct (IH _ _ _ _ _ _ Hlvl
                (Forall_inv_tail HO) (Forall_inv_tail H0)
                (Forall_inv_tail HS) (Forall_inv_tail HD) Hbytes HC Hwf')
      as (deltas & HF2 & Hwfend).
    exists (delta :: deltas).
    split; [|exact Hwfend].
    constructor; [apply HB0; exact (Forall_inv H0) | exact HF2].
Qed.

(** DstChain's endpoint through the packs: the prefix concatenates. *)
Lemma dstchain_concat : forall done evs deltas d0 d1,
  Forall2 (EvBits done) evs deltas ->
  DstChain evs d0 d1 ->
  d1 = d0 ++ concat deltas.
Proof.
  intros done evs deltas d0 d1 HF; revert d0 d1.
  induction HF as [|ev delta evs deltas HB HF IH]; intros d0 d1 HD.
  - cbn [DstChain] in HD. cbn [concat]. rewrite app_nil_r. exact HD.
  - cbn [DstChain] in HD.
    destruct HD as (He & HD).
    destruct HB as (Hdst & _).
    cbn [concat].
    rewrite (IH _ _ HD), Hdst, He, <- app_assoc.
    reflexivity.
Qed.

(* ==========================================================================
   4.  The body decodes.
   ========================================================================== *)

Theorem body_decodes : forall g wrap x sd s' evs0 evf body hdr,
  0 < dg_level g ->
  Forall (fun b => 0 <= b < 256) x ->
  Forall (EvOk g wrap (zs_done (d_strm s'))) (evs0 ++ [evf]) ->
  EvChain (evs0 ++ [evf]) (ts_bw (d_ts sd)) (zs_out (d_strm sd))
          (zs_availout (d_strm sd))
          (ts_bw (d_ts s')) (zs_out (d_strm s'))
          (zs_availout (d_strm s')) ->
  zs_out (d_strm sd) = hdr ->
  bw_out (ts_bw (d_ts sd)) = [] ->
  bw_valid (ts_bw (d_ts sd)) = 0 ->
  bw_buf (ts_bw (d_ts sd)) = 0 ->
  0 <= zs_availout (d_strm sd) ->
  Forall (fun e => fe_last e = 0) evs0 ->
  fe_last evf = 1 ->
  EvTile (evs0 ++ [evf]) 0 (zlen (zs_done (d_strm s'))) ->
  zs_done (d_strm s') = x ->
  zs_out (d_strm s') = hdr ++ body ->
  1 <= zs_availout (d_strm s') ->
  Forall ZR_SpanGuard (evs0 ++ [evf]) ->
  Forall (fun e => ZR_DynEntry (d_ts (fe_s e))) (evs0 ++ [evf]) ->
  BodyDecodesTo body x /\ IsValidStreamFor body x
  /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
      exists rem, dec_stream_from_strict (bytes_bits body) []
                  = Some (x, rem)
               /\ (length rem < 8)%nat).
Proof.
  intros g wrap x sd s' evs0 evf body hdr
         Hlvl Hx HO HC Houtsd Hbwsd Hbvsd Hbufsd Havosd0
         H0s Hl1 HT Edone Eout' Havo4 HS HD.
  (* byte-range at the final done *)
  assert (Hbytes : Forall (fun b => 0 <= b < 256) (zs_done (d_strm s')))
    by (rewrite Edone; exact Hx).
  (* the writer starts well-formed *)
  assert (Hwf0 : bw_wf (ts_bw (d_ts sd))).
  { unfold bw_wf. rewrite Hbvsd, Hbufsd.
    change Buf_size with 16. change (2 ^ 0) with 1. lia. }
  (* split the premise Foralls at the snoc *)
  apply Forall_app in HO; destruct HO as [HO0 HOf].
  apply Forall_app in HS; destruct HS as [HS0 HSf].
  apply Forall_app in HD; destruct HD as [HD0 HDf].
  apply Forall_inv in HOf. apply Forall_inv in HSf. apply Forall_inv in HDf.
  (* the last event pins the endpoint *)
  destruct (evchain_snoc_last _ _ _ _ _ _ _ _ HC) as (Ebw' & Eout2 & Eavo2).
  rewrite Hl1 in Ebw', Eout2, Eavo2.
  (* split the chain: a chain over evs0 into the final snapshot *)
  assert (Hchain0 : exists bwm outm avom,
      EvChain evs0 (ts_bw (d_ts sd)) (zs_out (d_strm sd))
              (zs_availout (d_strm sd)) bwm outm avom
      /\ ts_bw (d_ts (fe_s evf)) = bwm
      /\ zs_out (d_strm (fe_s evf)) = outm
      /\ zs_availout (d_strm (fe_s evf)) = avom).
  { clear -HC.
    revert HC.
    generalize (ts_bw (d_ts sd)) (zs_out (d_strm sd))
               (zs_availout (d_strm sd)).
    induction evs0 as [|e r IH]; intros bw out avo HC.
    - cbn [app EvChain] in HC.
      destruct HC as (Hb & Ho & Ha & _).
      exists bw, out, avo.
      split; [cbn [EvChain]; auto|auto].
    - cbn [app EvChain] in HC.
      destruct HC as (Hb & Ho & Ha & HC).
      destruct (IH _ _ _ HC) as (bwm & outm & avom & HC0 & E1 & E2 & E3).
      exists bwm, outm, avom.
      split; [|auto].
      cbn [EvChain]. auto. }
  destruct Hchain0 as (bwm & outm & avom & HC0 & Ebwm & Eoutm & Eavom).
  (* fold the 0-final prefix *)
  destruct (chain_bits g wrap (zs_done (d_strm s')) evs0 _ _ _ _ _ _
              Hlvl HO0 H0s HS0 HD0 Hbytes HC0 Hwf0)
    as (deltas0 & HF2 & Hwfm).
  (* the final event's pack *)
  destruct (event_bits g wrap (zs_done (d_strm s')) evf Hlvl
              HOf HSf HDf
              Hbytes ltac:(rewrite Ebwm; exact Hwfm))
    as (deltaf & Hdstf & _ & _ & HB1).
  destruct (HB1 Hl1) as (HFin & Hmod).
  rewrite Hl1 in Hdstf, Hmod.
  (* the dst chain and its endpoint *)
  pose proof (evchain_dst _ _ _ _ _ _ _ HC) as HDC.
  pose proof (evchain_dst _ _ _ _ _ _ _ HC0) as HDC0.
  assert (Edmid : bytes_bits outm ++ bw_stream bwm
                  = dst_stream (fe_s evf))
    by (unfold dst_stream; rewrite Ebwm, Eoutm; reflexivity).
  assert (Emid : dst_stream (fe_s evf)
                 = (bytes_bits (zs_out (d_strm sd))
                    ++ bw_stream (ts_bw (d_ts sd))) ++ concat deltas0).
  { rewrite <- Edmid.
    exact (dstchain_concat _ _ _ _ _ HF2 HDC0). }
  (* endpoint of the full chain = the final flush's dst *)
  assert (Edend : bytes_bits (zs_out (d_strm s')) ++ bw_stream (ts_bw (d_ts s'))
                  = dst_stream (fe_s evf) ++ deltaf).
  { rewrite <- Hdstf.
    unfold dst_stream. rewrite Ebw', Eout2. reflexivity. }
  (* the header side of dst sd *)
  assert (Ed0 : bytes_bits (zs_out (d_strm sd)) ++ bw_stream (ts_bw (d_ts sd))
                = bytes_bits hdr).
  { rewrite Houtsd. unfold bw_stream.
    rewrite Hbwsd, Hbvsd. rewrite zwrite_0.
    cbn [bytes_bits app]. rewrite !app_nil_r. reflexivity. }
  assert (Hhdr8 : (length (bytes_bits hdr) mod 8 = 0)%nat).
  { rewrite bytes_bits_length, Nat.mul_comm. apply Nat.Div0.mod_mul. }
  (* the writer is drained and aligned at s' *)
  assert (Hsnap0 : 0 <= zs_availout (d_strm (fe_s evf))).
  { pose proof (evchain_snapshots_avo _ _ _ _ _ _ _ Havosd0 HC) as HFa.
    apply Forall_app in HFa. destruct HFa as [_ HFa].
    apply Forall_inv in HFa. exact HFa. }
  assert (Hbw' : bw_out (ts_bw (d_ts s')) = []).
  { rewrite Ebw'.
    destruct (flush_block_only_shape 1 (fe_s evf) Hsnap0)
      as (mv & _ & _ & _ & Hd).
    apply Hd. rewrite <- Eavo2. lia. }
  assert (Hbv' : bw_valid (ts_bw (d_ts s')) = 0).
  { rewrite Ebw'. apply flush_block_only_last_valid.
    destruct HOf as (Hcf & _). rewrite Hcf. exact Hlvl. }
  assert (Ebits : bytes_bits body = concat deltas0 ++ deltaf).
  { assert (E1 : bytes_bits (zs_out (d_strm s'))
                 ++ bw_stream (ts_bw (d_ts s'))
                 = bytes_bits hdr ++ (concat deltas0 ++ deltaf)).
    { rewrite Edend, Emid, Ed0, <- app_assoc. reflexivity. }
    rewrite Eout' in E1.
    unfold bw_stream in E1.
    rewrite Hbw', Hbv', zwrite_0 in E1.
    cbn [bytes_bits] in E1.
    rewrite app_nil_l, app_nil_r in E1.
    rewrite bytes_bits_app in E1.
    apply app_inv_head in E1.
    exact E1. }
  (* the parity of the whole wire *)
  assert (Hpar : ((length (bytes_bits hdr)
                   + (length (concat deltas0) + length deltaf)) mod 8 = 0)%nat).
  { assert (Etot : dst_stream (flush_block_only 1 (fe_s evf))
                   = bytes_bits hdr ++ (concat deltas0 ++ deltaf)).
    { rewrite Hdstf, Emid, Ed0, <- app_assoc. reflexivity. }
    rewrite Etot in Hmod.
    rewrite !length_app in Hmod.
    exact Hmod. }
  (* the DstChain dec_blocks wants *)
  assert (HDCn : DstChain (evs0 ++ [evf]) (bytes_bits hdr)
                   ((bytes_bits hdr ++ concat deltas0) ++ deltaf)).
  { rewrite <- Ed0.
    replace ((bytes_bits (zs_out (d_strm sd))
              ++ bw_stream (ts_bw (d_ts sd))) ++ concat deltas0)
      with (dst_stream (fe_s evf)) by (rewrite Emid; reflexivity).
    replace (dst_stream (fe_s evf) ++ deltaf)
      with (bytes_bits (zs_out (d_strm s'))
            ++ bw_stream (ts_bw (d_ts s'))) by (rewrite Edend; reflexivity).
    exact HDC. }
  (* run the block fold *)
  destruct (dec_blocks evs0 evf deltas0 deltaf (zs_done (d_strm s'))
              0 (zlen (zs_done (d_strm s'))) (bytes_bits hdr)
              HF2 HFin HDCn HT Hpar)
    as (rem & Hdec & HdecsG & Hrlen).
  (* package: [rem] is the final windup pad, sub-byte by [dec_blocks] *)
  change (Z.to_nat 0) with 0%nat in Hdec.
  rewrite firstn_O in Hdec.
  rewrite Edone in Hdec.
  assert (Efn : firstn (Z.to_nat (zlen x)) x = x).
  { unfold zlen. rewrite Nat2Z.id. apply firstn_all. }
  rewrite Efn in Hdec.
  split; [|split].
  - unfold BodyDecodesTo, dec_stream, dec_stream_rem.
    rewrite Ebits.
    rewrite Hdec.
    reflexivity.
  - unfold IsValidStreamFor, dec_stream_rem.
    exists rem.
    split; [|exact Hrlen].
    rewrite Ebits.
    exact Hdec.
  - intros HBK EFR.
    pose proof (HdecsG HBK EFR) as Hdecs.
    change (Z.to_nat 0) with 0%nat in Hdecs.
    rewrite firstn_O in Hdecs.
    rewrite Edone in Hdecs.
    rewrite Efn in Hdecs.
    exists rem.
    split; [|exact Hrlen].
    rewrite Ebits.
    exact Hdecs.
Qed.

Print Assumptions body_decodes.
