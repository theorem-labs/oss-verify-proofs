(** * ZREmitBytes — every byte the emitter writes is a byte.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).  G5, part 7.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [ZR_EmitterPublishes] carries a [Forall (0 <= _ < 256)] clause over
    the emitted stream (the inflater faces consume it — the Q6 raw face
    threads the same premise).  The pending queue only ever grows by
    [u8]-masked pushes ([bw_put_byte]/[bw_put_short]/[map u8]), so
    [BwBytes] (queue content in range) is preserved by every emit
    operation, and the output — which [flush_pending] moves out of the
    queue — inherits it along the [EvChain].  Mechanical; no walk facts
    consumed beyond the chain itself. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwEv SwStep BtFrame.
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
       set_matches set_symnext set_statlen set_optlen set_tree
       bw_out bw_buf bw_valid c_sx c_bw].

(* ==========================================================================
   1.  The queue-content invariant and the primitive pushes.
   ========================================================================== *)

Definition BwBytes (b : BW) : Prop :=
  Forall (fun v => 0 <= v < 256) (bw_out b).

Lemma u8_range : forall v, 0 <= u8 v < 256.
Proof. intro v. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma forall_firstn : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l H.
  rewrite <- (firstn_skipn n l) in H.
  apply Forall_app in H. tauto.
Qed.

Lemma forall_skipn : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros P n l H.
  rewrite <- (firstn_skipn n l) in H.
  apply Forall_app in H. tauto.
Qed.

Lemma bwb_put_byte : forall v b, BwBytes b -> BwBytes (bw_put_byte v b).
Proof.
  intros v b H. unfold BwBytes, bw_put_byte in *. cbn [bw_out].
  apply Forall_app. split; [exact H|].
  constructor; [apply u8_range | constructor].
Qed.

Lemma bwb_put_short : forall w b, BwBytes b -> BwBytes (bw_put_short w b).
Proof.
  intros w b H. unfold bw_put_short. auto using bwb_put_byte.
Qed.

Lemma bwb_flush : forall b, BwBytes b -> BwBytes (bw_flush b).
Proof.
  intros b H. unfold bw_flush.
  destruct (Z.eqb (bw_valid b) 16).
  - unfold BwBytes. cbn [bw_out].
    exact (bwb_put_short (bw_buf b) b H).
  - destruct (Z.leb 8 (bw_valid b)).
    + unfold BwBytes. cbn [bw_out].
      exact (bwb_put_byte (bw_buf b) b H).
    + exact H.
Qed.

Lemma bwb_windup : forall b, BwBytes b -> BwBytes (bw_windup b).
Proof.
  intros b H. unfold bw_windup. cbv zeta.
  unfold BwBytes. cbn [bw_out].
  destruct (Z.ltb 8 (bw_valid b)).
  - exact (bwb_put_short (bw_buf b) b H).
  - destruct (Z.ltb 0 (bw_valid b)).
    + exact (bwb_put_byte (bw_buf b) b H).
    + exact H.
Qed.

Lemma bwb_send_bits : forall v n b, BwBytes b -> BwBytes (bw_send_bits v n b).
Proof.
  intros v n b H. unfold bw_send_bits. cbv zeta.
  destruct (Z.ltb (Buf_size - n) (bw_valid b)).
  - unfold BwBytes. cbn [bw_out].
    exact (bwb_put_short _ b H).
  - exact H.
Qed.

Lemma bwb_send_code : forall c t b, BwBytes b -> BwBytes (send_code c t b).
Proof. intros c t b H. unfold send_code. apply bwb_send_bits. exact H. Qed.

(* ==========================================================================
   2.  The tree-emit recursors.
   ========================================================================== *)

Lemma bwb_send_rep : forall f c bl count b,
  BwBytes b -> BwBytes (send_rep f c bl count b).
Proof.
  induction f as [|f IH]; intros c bl count b H; cbn [send_rep].
  - exact H.
  - destruct (Z.eqb (count - 1) 0).
    + apply bwb_send_code. exact H.
    + apply IH. apply bwb_send_code. exact H.
Qed.

Lemma bwb_send_go : forall f t maxc n prevlen nextlen count maxcnt mincnt bl b,
  BwBytes b ->
  BwBytes (send_go f t maxc n prevlen nextlen count maxcnt mincnt bl b).
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl b H;
    cbn [send_go].
  - exact H.
  - destruct (Z.ltb maxc n); [exact H|].
    destruct ((Z.ltb (count + 1) maxcnt)
              && (Z.eqb nextlen (t_len t (n + 1)))).
    + apply IH. exact H.
    + apply IH.
      destruct (Z.ltb (count + 1) mincnt).
      { apply bwb_send_rep. exact H. }
      destruct (negb (Z.eqb nextlen 0)).
      { destruct (negb (Z.eqb nextlen prevlen)); cbn [fst snd];
          apply bwb_send_bits; repeat apply bwb_send_code; exact H. }
      destruct (Z.leb (count + 1) 10);
        apply bwb_send_bits; apply bwb_send_code; exact H.
Qed.

Lemma bwb_send_tree : forall t maxc bl b,
  BwBytes b -> BwBytes (send_tree t maxc bl b).
Proof.
  intros t maxc bl b H. unfold send_tree. cbv zeta.
  apply bwb_send_go. exact H.
Qed.

Lemma bwb_sat_ranks : forall f rank blcodes bl b,
  BwBytes b -> BwBytes (sat_ranks f rank blcodes bl b).
Proof.
  induction f as [|f IH]; intros rank blcodes bl b H; cbn [sat_ranks].
  - exact H.
  - destruct (Z.leb blcodes rank); [exact H|].
    apply IH. apply bwb_send_bits. exact H.
Qed.

Lemma bwb_send_all_trees : forall lc dc blc s,
  BwBytes (ts_bw s) -> BwBytes (send_all_trees lc dc blc s).
Proof.
  intros lc dc blc s H. unfold send_all_trees. cbv zeta.
  apply bwb_send_tree. apply bwb_send_tree. apply bwb_sat_ranks.
  repeat apply bwb_send_bits. exact H.
Qed.

Lemma bwb_cb_step : forall sym symnext lt dt st,
  BwBytes (c_bw st) ->
  match cb_step sym symnext lt dt st with
  | CbCont st' => BwBytes (c_bw st')
  | CbDone st' => BwBytes (c_bw st')
  end.
Proof.
  intros sym symnext lt dt st H.
  unfold cb_step. cbv zeta.
  match goal with
  | |- match (if ?c then _ else _) with _ => _ end => destruct c
  end; tsimp;
    repeat first
      [ exact H
      | apply bwb_send_bits
      | apply bwb_send_code
      | match goal with |- BwBytes (if ?c then _ else _) => destruct c end ].
Qed.

Lemma bwb_cb_iter : forall j sym symnext lt dt st,
  BwBytes (c_bw st) ->
  match cb_iter j sym symnext lt dt st with
  | Some st' => BwBytes (c_bw st')
  | None => True
  end.
Proof.
  induction j as [|j IH]; intros sym symnext lt dt st H; cbn [cb_iter].
  - exact H.
  - pose proof (bwb_cb_step sym symnext lt dt st H) as HS.
    destruct (cb_step sym symnext lt dt st) as [st'|st'].
    + exact (IH sym symnext lt dt st' HS).
    + exact I.
Qed.

Lemma bwb_cb_loop : forall f sym symnext lt dt st,
  BwBytes (c_bw st) ->
  match cb_loop f sym symnext lt dt st with
  | Some st' => BwBytes (c_bw st')
  | None => True
  end.
Proof.
  induction f as [|f IH]; intros sym symnext lt dt st H; cbn [cb_loop].
  - exact I.
  - pose proof (bwb_cb_step sym symnext lt dt st H) as HS.
    destruct (cb_step sym symnext lt dt st) as [st'|st'].
    + exact (IH sym symnext lt dt st' HS).
    + exact HS.
Qed.

Lemma bwb_compress_block : forall sym symnext lt dt b,
  BwBytes b -> BwBytes (compress_block sym symnext lt dt b).
Proof.
  intros sym symnext lt dt b H. unfold compress_block. cbv zeta.
  apply bwb_send_code.
  destruct (Z.eqb symnext 0); [exact H|].
  pose proof (bwb_cb_loop (Z.to_nat symnext + 1) sym symnext lt dt
                {| c_sx := 0; c_bw := b |} ltac:(tsimp; exact H)) as HL.
  destruct (cb_loop (Z.to_nat symnext + 1) sym symnext lt dt
              {| c_sx := 0; c_bw := b |}) as [st|].
  - exact HL.
  - exact H.
Qed.

Lemma bwb_tr_stored_block : forall dat sl last s,
  BwBytes (ts_bw s) -> BwBytes (ts_bw (tr_stored_block dat sl last s)).
Proof.
  intros dat sl last s H. unfold tr_stored_block. cbv zeta. tsimp.
  unfold BwBytes. cbn [bw_out].
  apply Forall_app. split.
  - exact (bwb_put_short _ _ (bwb_put_short _ _
             (bwb_windup _ (bwb_send_bits _ _ _ H)))).
  - apply Forall_forall. intros v Hv.
    apply in_map_iff in Hv. destruct Hv as (w & <- & _).
    apply u8_range.
Qed.

Lemma ts_bw_init_block : forall s, ts_bw (init_block s) = ts_bw s.
Proof. intro s. unfold init_block. cbv zeta. tsimp. reflexivity. Qed.

(* ==========================================================================
   3.  The block flush and the pending drain.
   ========================================================================== *)

Lemma bwb_tr_flush_block : forall buf sl last lvl strat dt ts0,
  BwBytes (ts_bw ts0) ->
  BwBytes (ts_bw (snd (tr_flush_block buf sl last lvl strat dt ts0))).
Proof.
  intros buf sl last lvl strat dt ts0 H.
  assert (HS4 : forall s4, BwBytes (ts_bw s4) ->
      BwBytes (ts_bw (if Z.eqb last 0 then init_block s4
                      else set_bw (bw_windup (ts_bw (init_block s4)))
                                  (init_block s4)))).
  { intros s4 H4. destruct (Z.eqb last 0).
    - rewrite ts_bw_init_block. exact H4.
    - tsimp. apply bwb_windup. rewrite ts_bw_init_block. exact H4. }
  unfold tr_flush_block.
  destruct (build_tree_frame TK_L ts0) as (_ & _ & EbwL & _).
  destruct (build_tree_frame TK_D (build_tree TK_L ts0)) as (_ & _ & EbwD & _).
  destruct (build_bl_tree_frame (build_tree TK_D (build_tree TK_L ts0)))
    as (_ & _ & EbwB & _).
  assert (H2 : BwBytes (ts_bw (snd (build_bl_tree
                  (build_tree TK_D (build_tree TK_L ts0)))))).
  { unfold BwBytes. rewrite EbwB, EbwD, EbwL. exact H. }
  destruct (Z.ltb 0 lvl); cbv zeta; cbn [snd]; apply HS4.
  - (* level > 0: stored / static / dynamic *)
    destruct buf as [dat|]; cbv iota.
    + match goal with
      | |- context [if ?c then Some _ else None] => destruct c
      end; cbv iota.
      * apply bwb_tr_stored_block. exact H2.
      * match goal with
        | |- BwBytes (ts_bw (if ?c then _ else _)) => destruct c
        end; tsimp; apply bwb_compress_block.
        -- apply bwb_send_bits. exact H2.
        -- apply bwb_send_all_trees. tsimp. apply bwb_send_bits. exact H2.
    + match goal with
      | |- BwBytes (ts_bw (if ?c then _ else _)) => destruct c
      end; tsimp; apply bwb_compress_block.
      * apply bwb_send_bits. exact H2.
      * apply bwb_send_all_trees. tsimp. apply bwb_send_bits. exact H2.
  - (* level = 0: forced stored *)
    destruct buf as [dat|]; cbv iota.
    + match goal with
      | |- BwBytes (ts_bw (if ?c then _ else _)) => destruct c
      end.
      * apply bwb_tr_stored_block. exact H.
      * exact H.
    + tsimp. apply bwb_compress_block. apply bwb_send_bits. exact H.
Qed.

(* ==========================================================================
   3.  The pending drain and the flush event.
   ========================================================================== *)

Lemma flush_pending_bytes : forall s,
  BwBytes (ts_bw (d_ts s)) ->
  Forall (fun v => 0 <= v < 256) (zs_out (d_strm s)) ->
  Forall (fun v => 0 <= v < 256) (zs_out (d_strm (flush_pending s)))
  /\ BwBytes (ts_bw (d_ts (flush_pending s))).
Proof.
  intros s Hbw Hout.
  assert (Hfb : BwBytes (ts_bw (tr_flush_bits (d_ts s)))).
  { unfold tr_flush_bits. tsimp. apply bwb_flush. exact Hbw. }
  unfold flush_pending. cbv zeta.
  destruct (Z.eqb _ 0).
  - dsimp. split; [exact Hout | exact Hfb].
  - dsimp. tsimp.
    split.
    + apply Forall_app. split; [exact Hout|].
      apply forall_firstn. exact Hfb.
    + unfold BwBytes. cbn [bw_out].
      apply forall_skipn. exact Hfb.
Qed.

Lemma flush_block_only_bytes : forall l s,
  BwBytes (ts_bw (d_ts s)) ->
  Forall (fun v => 0 <= v < 256) (zs_out (d_strm s)) ->
  Forall (fun v => 0 <= v < 256) (zs_out (d_strm (flush_block_only l s)))
  /\ BwBytes (ts_bw (d_ts (flush_block_only l s))).
Proof.
  intros l s Hbw Hout.
  unfold flush_block_only. cbv zeta.
  match goal with
  | |- context [flush_pending ?X] => set (s2 := X)
  end.
  apply flush_pending_bytes.
  - unfold s2. dsimp. apply bwb_tr_flush_block. exact Hbw.
  - unfold s2. dsimp. exact Hout.
Qed.

(* ==========================================================================
   4.  Along the chain: the whole output stays in range.
   ========================================================================== *)

Lemma evchain_out_bytes : forall evs bw out avo bw' out' avo',
  EvChain evs bw out avo bw' out' avo' ->
  BwBytes bw ->
  Forall (fun v => 0 <= v < 256) out ->
  Forall (fun v => 0 <= v < 256) out' /\ BwBytes bw'.
Proof.
  induction evs as [|ev evs IH]; intros bw out avo bw' out' avo' HC Hbw Hout.
  - cbn [EvChain] in HC. destruct HC as (-> & -> & _).
    split; [exact Hout | exact Hbw].
  - cbn [EvChain] in HC.
    destruct HC as (Hb & Ho & Ha & HC).
    destruct (flush_block_only_bytes (fe_last ev) (fe_s ev)
                ltac:(rewrite Hb; exact Hbw)
                ltac:(rewrite Ho; exact Hout)) as (Ho' & Hb').
    exact (IH _ _ _ _ _ _ HC Hb' Ho').
Qed.

Print Assumptions evchain_out_bytes.
