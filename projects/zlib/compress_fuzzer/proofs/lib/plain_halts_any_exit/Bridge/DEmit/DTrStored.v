(** * Bridge.DEmit.DTrStored — pair D24 of PAIRS.md: [_tr_stored_block], S5 vs RT.

    S5 ([Z/Trees.v:447]): three header bits, [bi_windup], [LEN] and [NLEN] as two
    [put_short]s, then [stored_len] window bytes copied into [pending_buf] at
    [pending] ([arr_blit]) and [pending += stored_len].  RT ([Trees.v:956]): the
    same four emitters on its [BW] queue, then [bw_out ++ map u8 dat], where the
    caller hands it the bytes [dat] (deflate_stored: [win_take] of the window).

    Delivered:
    - [bw4]: the frame of an S5 bit-writer operation (only [pending_buf],
      [pending], [bi_buf], [bi_valid] change; the buffer keeps its length; the
      queue only grows; only the appended region of the buffer is written), with
      its closure under [send_bits], [bi_windup], [put_short] and
      [tr_stored_block];
    - [br_tr_stored_block]: [bw_rel] is preserved (the bit-writer half);
    - [pair_tr_stored_block]: [dst_rel] is preserved when no symbol is pending
      ([sym_next = 0]: the copy may land in the symbol area of S5's aliased
      [pending_buf]), the call site of [deflate_stored].

    Side conditions, each needed (probes in section 5):
    - [pending_out = 0] and the final [pending] inside the buffer: BrBits's
      [room], once for the whole block (S5's own safety proofs establish exactly
      [ds_pending (tr_stored_block ..) <= pending_buf_size]);
    - the copied bytes are bytes: S5 copies window values as they are, RT stores
      [u8] of each.

    Ownership: a worker (group D).  Reviewer: a worker. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.

(* ------------------------------------------------------------------------- *)
(* 1.  Slice kit for the copy                                                *)
(* ------------------------------------------------------------------------- *)

Lemma slice_nat_app : forall {A} n m (a : parr A) o,
  arr_slice_nat a o (n + m) = arr_slice_nat a o n ++ arr_slice_nat a (o + Z.of_nat n) m.
Proof.
  induction n as [|n IH]; intros m a o.
  - cbn [arr_slice_nat Nat.add app]. rewrite Z.add_0_r. reflexivity.
  - cbn [arr_slice_nat Nat.add app]. rewrite IH. do 3 f_equal. lia.
Qed.

Lemma slice_nat_ext : forall {A} n (a b : parr A) o o',
  (forall k, (k < n)%nat -> arr_get a (o + Z.of_nat k) = arr_get b (o' + Z.of_nat k)) ->
  arr_slice_nat a o n = arr_slice_nat b o' n.
Proof.
  induction n as [|n IH]; intros a b o o' H; [reflexivity|].
  cbn [arr_slice_nat]. f_equal.
  - pose proof (H 0%nat ltac:(lia)) as H0. rewrite !Z.add_0_r in H0. exact H0.
  - apply IH. intros k Hk. pose proof (H (S k) ltac:(lia)) as Hs.
    replace (o + 1 + Z.of_nat k) with (o + Z.of_nat (S k)) by lia.
    replace (o' + 1 + Z.of_nat k) with (o' + Z.of_nat (S k)) by lia. exact Hs.
Qed.

(** Copying [len] source values to the tail [p] of a queue that starts at 0
    extends the queue by them. *)
Lemma slice_blit0 : forall (a src : arr) p off len,
  0 <= p -> 0 <= len -> p + len <= arr_len a ->
  arr_slice (arr_blit a p src off len) 0 (p + len) = arr_slice a 0 p ++ arr_slice src off len.
Proof.
  intros a src p off len Hp Hl Hin. unfold arr_slice.
  replace (Z.to_nat (p + len)) with (Z.to_nat p + Z.to_nat len)%nat by lia.
  rewrite slice_nat_app. f_equal.
  - apply slice_nat_ext. intros k Hk. rewrite arr_get_blit.
    destruct (p <=? 0 + Z.of_nat k) eqn:E; [apply Z.leb_le in E; lia|]. reflexivity.
  - apply slice_nat_ext. intros k Hk. rewrite arr_get_blit. unfold arr_inb.
    replace (p <=? 0 + Z.of_nat (Z.to_nat p) + Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
    replace (0 + Z.of_nat (Z.to_nat p) + Z.of_nat k <? p + Z.max 0 len) with true
      by (symmetry; apply Z.ltb_lt; lia).
    replace (0 <=? 0 + Z.of_nat (Z.to_nat p) + Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
    replace (0 + Z.of_nat (Z.to_nat p) + Z.of_nat k <? arr_len a) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb]. f_equal. lia.
Qed.

Lemma map_u8_bytes : forall l, Forall (fun v => 0 <= v < 256) l -> map Base.u8 l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  inversion H as [|? ? Hx Hl]; subst. cbn [map]. rewrite IH by exact Hl.
  unfold Base.u8. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma bw_put_short_u16 : forall w b, ZBitsOut.bw_put_short (Base.u16 w) b = ZBitsOut.bw_put_short w b.
Proof.
  intros w b. unfold ZBitsOut.bw_put_short, ZBitsOut.bw_put_byte. f_equal.
  cbn [ZBitsOut.bw_out]. unfold Base.u8, Base.u16.
  rewrite Z.mod_mod by lia.
  assert (E : w mod 65536 mod 256 = w mod 256).
  { symmetry. rewrite (Z.div_mod w 65536) at 1 by lia.
    replace (65536 * (w / 65536) + w mod 65536) with (w mod 65536 + (w / 65536 * 256) * 256) by lia.
    apply Z.mod_add. lia. }
  rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The frame of an S5 bit-writer operation                               *)
(* ------------------------------------------------------------------------- *)

Definition set4 (s : DS.deflate_state) (pb : arr) (p bb bv : Z) : DS.deflate_state :=
  DS.set_bi_valid (DS.set_bi_buf (DS.set_pending (DS.set_pending_buf s pb) p) bb) bv.

(** [s'] is [s] with only the four bit-writer fields changed, the buffer keeps
    its length, the queue only grows, and only its appended region is
    written. *)
Definition bw4 (s s' : DS.deflate_state) : Prop :=
  s' = set4 s (DS.ds_pending_buf s') (DS.ds_pending s') (DS.ds_bi_buf s') (DS.ds_bi_valid s')
  /\ arr_len (DS.ds_pending_buf s') = arr_len (DS.ds_pending_buf s)
  /\ DS.ds_pending s <= DS.ds_pending s'
  /\ (forall i, i < DS.ds_pending s \/ DS.ds_pending s' <= i ->
        arr_get (DS.ds_pending_buf s') i = arr_get (DS.ds_pending_buf s) i).

Ltac s5bw := autorewrite with s5f_bi_valid s5f_bi_buf s5f_pending s5f_pending_buf.

Lemma bw4_refl : forall s, bw4 s s.
Proof.
  intros s. unfold bw4, set4. split; [destruct s; reflexivity|]. split; [reflexivity|]. split; [lia|].
  intros i _. reflexivity.
Qed.

Lemma bw4_trans : forall s1 s2 s3, bw4 s1 s2 -> bw4 s2 s3 -> bw4 s1 s3.
Proof.
  intros s1 s2 s3 (E2 & L2 & P2 & G2) (E3 & L3 & P3 & G3).
  split; [|split; [lia|split; [lia|]]].
  - rewrite E3 at 1. rewrite E2 at 1. unfold set4. destruct s1; reflexivity.
  - intros i Hi. rewrite G3 by lia. apply G2. lia.
Qed.

Lemma bw4_set_bi_buf : forall s v, bw4 s (DS.set_bi_buf s v).
Proof.
  intros s v. unfold bw4, set4. s5bw. split; [destruct s; reflexivity|].
  split; [reflexivity|]. split; [lia|]. intros i _. reflexivity.
Qed.

Lemma bw4_set_bi_valid : forall s v, bw4 s (DS.set_bi_valid s v).
Proof.
  intros s v. unfold bw4, set4. s5bw. split; [destruct s; reflexivity|].
  split; [reflexivity|]. split; [lia|]. intros i _. reflexivity.
Qed.

Lemma bw4_put_byte : forall s c, bw4 s (DS.put_byte s c).
Proof.
  intros s c. unfold bw4, set4, DS.put_byte. cbv zeta. s5bw.
  split; [destruct s; reflexivity|].
  split; [apply arr_len_set|]. split; [lia|].
  intros i Hi. apply arr_get_set_other. lia.
Qed.

Lemma bw4_put_short : forall s w, bw4 s (DT.put_short s w).
Proof.
  intros s w. unfold DT.put_short. cbv zeta.
  eapply bw4_trans; [apply bw4_put_byte | apply bw4_put_byte].
Qed.

Lemma bw4_send_bits : forall s v l, bw4 s (DT.send_bits s v l).
Proof.
  intros s v l. unfold DT.send_bits. cbv zeta.
  destruct (DS.Buf_size - l <? DS.ds_bi_valid s).
  - eapply bw4_trans; [apply bw4_set_bi_buf|].
    eapply bw4_trans; [apply bw4_put_short|].
    eapply bw4_trans; [apply bw4_set_bi_buf | apply bw4_set_bi_valid].
  - eapply bw4_trans; [apply bw4_set_bi_buf | apply bw4_set_bi_valid].
Qed.

Lemma bw4_bi_windup : forall s, bw4 s (DT.bi_windup s).
Proof.
  intros s. unfold DT.bi_windup. cbv zeta.
  destruct (8 <? DS.ds_bi_valid s).
  - eapply bw4_trans; [apply bw4_put_short|].
    eapply bw4_trans; [apply bw4_set_bi_buf | apply bw4_set_bi_valid].
  - destruct (0 <? DS.ds_bi_valid s).
    + eapply bw4_trans; [apply bw4_put_byte|].
      eapply bw4_trans; [apply bw4_set_bi_buf | apply bw4_set_bi_valid].
    + eapply bw4_trans; [apply bw4_set_bi_buf | apply bw4_set_bi_valid].
Qed.

Lemma pend_put_short : forall s w, DS.ds_pending (DT.put_short s w) = DS.ds_pending s + 2.
Proof.
  intros s w. unfold DT.put_short, DS.put_byte. cbv zeta. s5bw. lia.
Qed.

(** The copy step (S5 copies only for a non-empty block with a source). *)
Definition tsb_copy (s : DS.deflate_state) (buf : option Z) (len : Z) : DS.deflate_state :=
  if negb (len =? 0) then
    match buf with
    | Some off => DS.set_pending_buf s (arr_blit (DS.ds_pending_buf s) (DS.ds_pending s) (DS.ds_window s) off len)
    | None => s
    end
  else s.

Lemma pend_tsb_copy : forall s buf len, DS.ds_pending (tsb_copy s buf len) = DS.ds_pending s.
Proof.
  intros s buf len. unfold tsb_copy. destruct (negb (len =? 0)); [destruct buf|]; s5bw; reflexivity.
Qed.

(** The copy step and the final [pending] update. *)
Lemma bw4_copy : forall s (buf : option Z) len, 0 <= len ->
  bw4 s (DS.set_pending (tsb_copy s buf len) (DS.ds_pending (tsb_copy s buf len) + len)).
Proof.
  intros s buf len Hl. rewrite pend_tsb_copy. unfold tsb_copy.
  destruct (negb (len =? 0)); [destruct buf as [off|]|]; unfold bw4, set4; s5bw.
  - split; [destruct s; reflexivity|]. split; [apply arr_len_blit|]. split; [lia|].
    intros i Hi. rewrite arr_get_blit.
    destruct (DS.ds_pending s <=? i) eqn:E1; [|reflexivity].
    destruct (i <? DS.ds_pending s + Z.max 0 len) eqn:E2; [|reflexivity].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - split; [destruct s; reflexivity|]. split; [reflexivity|]. split; [lia|]. intros i _. reflexivity.
  - split; [destruct s; reflexivity|]. split; [reflexivity|]. split; [lia|]. intros i _. reflexivity.
Qed.

(** [tr_stored_block] as the composition of its steps.  The final [pending]
    update reads the copied state, exactly as S5 writes it. *)
Lemma tsb_unfold : forall s buf len last,
  DT.tr_stored_block s buf len last =
  (let s4 := DT.put_short (DT.put_short (DT.bi_windup (DT.send_bits s (Z.shiftl DS.STORED_BLOCK 1 + last) 3))
                                        (wrap16 len)) (wrap16 (Z.lnot len)) in
   DS.set_pending (tsb_copy s4 buf len) (DS.ds_pending (tsb_copy s4 buf len) + len)).
Proof. intros. unfold DT.tr_stored_block, tsb_copy. reflexivity. Qed.

Theorem bw4_tr_stored_block : forall s buf len last, 0 <= len ->
  bw4 s (DT.tr_stored_block s buf len last).
Proof.
  intros s buf len last Hl. rewrite tsb_unfold. cbv zeta.
  eapply bw4_trans; [|apply (bw4_copy _ buf len Hl)].
  eapply bw4_trans; [apply bw4_send_bits|].
  eapply bw4_trans; [apply bw4_bi_windup|].
  eapply bw4_trans; [apply bw4_put_short | apply bw4_put_short].
Qed.

(** The final [pending]: the header's, plus the four length bytes, plus the copy. *)
Lemma tsb_pending : forall s buf len last,
  DS.ds_pending (DT.tr_stored_block s buf len last)
  = DS.ds_pending (DT.bi_windup (DT.send_bits s (Z.shiftl DS.STORED_BLOCK 1 + last) 3)) + 4 + len.
Proof.
  intros s buf len last. rewrite tsb_unfold. cbv zeta. s5bw.
  rewrite pend_tsb_copy, !pend_put_short. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The bit-writer half                                                   *)
(* ------------------------------------------------------------------------- *)

(** Where the copied bytes come from, on S5's side. *)
Definition stored_src (s : DS.deflate_state) (buf : option Z) (len : Z) (dat : list Z) : Prop :=
  match buf with
  | Some off => 0 <= off /\ off + len <= arr_len (DS.ds_window s)
                /\ arr_slice (DS.ds_window s) off len = dat
                /\ Forall (fun v => 0 <= v < 256) dat
  | None => len = 0 /\ dat = []
  end.

Lemma pend_rel_len : forall s out, pend_rel s out -> Z.of_nat (length out) = DS.ds_pending s.
Proof.
  intros s out (H1 & H2 & H3 & <-). unfold arr_slice.
  assert (G : forall n (a : arr) o, length (arr_slice_nat a o n) = n)
    by (induction n as [|n IH]; intros a o; [reflexivity | cbn [arr_slice_nat length]; rewrite IH; reflexivity]).
  rewrite G. lia.
Qed.

Theorem br_tr_stored_block : forall s ts buf len last dat,
  bw_rel s (RT.ts_bw ts) ->
  DS.ds_pending_out s = 0 ->
  DS.ds_pending (DT.tr_stored_block s buf len last) <= arr_len (DS.ds_pending_buf s) ->
  0 <= len ->
  stored_src s buf len dat ->
  bw_rel (DT.tr_stored_block s buf len last) (RT.ts_bw (RT.tr_stored_block dat len last ts)).
Proof.
  intros s ts buf len last dat Hb Hpo Hfin Hl Hsrc.
  rewrite tsb_pending in Hfin.
  unfold RT.tr_stored_block. cbn [RT.ts_bw RT.set_bw].
  rewrite tsb_unfold. cbv zeta.
  change (Z.shiftl RT.STORED_BLOCK 1 + last) with (Z.shiftl DS.STORED_BLOCK 1 + last).
  set (v := Z.shiftl DS.STORED_BLOCK 1 + last) in *.
  (* step 1: three header bits *)
  pose proof (bw4_send_bits s v 3) as F1.
  pose proof (bw4_bi_windup (DT.send_bits s v 3)) as F2.
  assert (R1 : room s 2).
  { destruct F1 as (_ & _ & P1 & _). destruct F2 as (_ & _ & P2 & _). split; [exact Hpo | lia]. }
  pose proof (br_send_bits s _ v 3 Hb R1) as B1.
  revert F1 F2 B1 Hfin. generalize (DT.send_bits s v 3). intros s1 F1 F2 B1 Hfin.
  (* step 2: windup *)
  assert (R2 : room s1 2).
  { destruct F1 as (E1 & L1 & _ & _). destruct F2 as (_ & L2 & P2 & _).
    split; [rewrite E1; unfold set4; s5bw; exact Hpo | lia]. }
  pose proof (br_bi_windup s1 _ B1 R2) as B2.
  revert F2 B2 Hfin. generalize (DT.bi_windup s1). intros s2 F2 B2 Hfin.
  pose proof (bw4_trans _ _ _ F1 F2) as F12. clear F1 F2.
  (* step 3: LEN, NLEN *)
  assert (Hpo2 : DS.ds_pending_out s2 = 0).
  { destruct F12 as (E & _). rewrite E. unfold set4. s5bw. exact Hpo. }
  assert (L2 : arr_len (DS.ds_pending_buf s2) = arr_len (DS.ds_pending_buf s))
    by (destruct F12 as (_ & L & _); exact L).
  assert (R3 : room s2 2) by (split; [exact Hpo2 | lia]).
  pose proof (br_put_short s2 _ (wrap16 len) B2 R3) as B3.
  pose proof (bw4_put_short s2 (wrap16 len)) as F3.
  pose proof (pend_put_short s2 (wrap16 len)) as P3.
  revert F3 B3 P3. generalize (DT.put_short s2 (wrap16 len)). intros s3 F3 B3 P3.
  assert (Hpo3 : DS.ds_pending_out s3 = 0).
  { destruct F3 as (E & _). rewrite E. unfold set4. s5bw. exact Hpo2. }
  assert (L3 : arr_len (DS.ds_pending_buf s3) = arr_len (DS.ds_pending_buf s)) by (destruct F3 as (_ & L & _); lia).
  assert (R4 : room s3 2) by (split; [exact Hpo3 | lia]).
  pose proof (br_put_short s3 _ (wrap16 (Z.lnot len)) B3 R4) as B4.
  pose proof (bw4_put_short s3 (wrap16 (Z.lnot len))) as F4.
  pose proof (pend_put_short s3 (wrap16 (Z.lnot len))) as P4.
  revert F4 B4 P4. generalize (DT.put_short s3 (wrap16 (Z.lnot len))). intros s4 F4 B4 P4.
  assert (Hpo4 : DS.ds_pending_out s4 = 0).
  { destruct F4 as (E & _). rewrite E. unfold set4. s5bw. exact Hpo3. }
  assert (L4 : arr_len (DS.ds_pending_buf s4) = arr_len (DS.ds_pending_buf s)) by (destruct F4 as (_ & L & _); lia).
  assert (W4 : DS.ds_window s4 = DS.ds_window s).
  { destruct F12 as (E2 & _). destruct F3 as (E3 & _). destruct F4 as (E4 & _).
    rewrite E4. unfold set4. s5bw. rewrite E3. unfold set4. s5bw. rewrite E2. unfold set4. s5bw. reflexivity. }
  rewrite !wrap16_u16 in B4. rewrite (bw_put_short_u16 len) in B4.
  replace (Z.lnot len) with (- len - 1) in B4 by (pose proof (Z.add_lnot_diag len); lia).
  (* step 4: the copy *)
  destruct B4 as (Hp4 & Hb4 & Hv4).
  rewrite pend_tsb_copy. unfold tsb_copy.
  unfold bw_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
  destruct (Z.eqb_spec len 0) as [Z0|NZ].
  - subst len. cbn [negb].
    assert (Edat : dat = []).
    { destruct buf as [off|]; [destruct Hsrc as (_ & _ & <- & _); reflexivity | destruct Hsrc as (_ & Hd); exact Hd]. }
    subst dat. cbn [map]. rewrite app_nil_r.
    destruct Hp4 as (Hpo' & Hp' & Hin' & Hsl'). unfold pend_rel. s5bw. rewrite Z.add_0_r.
    split; [split; [lia|split; [lia|split; [lia|exact Hsl']]]|split; assumption].
  -
    destruct buf as [off|]; [|destruct Hsrc as (Hz & _); lia].
    cbn [negb].
    destruct Hsrc as (Ho & Hoe & Hsl & Hby).
    destruct Hp4 as (Hpo' & Hp' & Hin' & Hsl').
    unfold pend_rel. s5bw. rewrite arr_len_blit. rewrite Hpo4 in *.
    split; [split; [lia|split; [lia|split; [lia|]]]|split; assumption].
    rewrite slice_blit0 by lia. rewrite Hsl', W4, Hsl, map_u8_bytes by exact Hby. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The pair at the deflate relation                                      *)
(* ------------------------------------------------------------------------- *)

(** Where the copied bytes come from, on RT's side: [win_take] of the window,
    as RT's [deflate_stored] hands them over, and they are bytes. *)
Definition stored_src_rt (t : RD.DSt) (buf : option Z) (len : Z) (dat : list Z) : Prop :=
  match buf with
  | Some off => 0 <= off /\ off + len <= RD.ls_windowsize (RD.d_ls t)
                /\ dat = RD.win_take (RD.ls_window (RD.d_ls t)) off len
                /\ (forall i, off <= i < off + len -> 0 <= RD.ls_window (RD.d_ls t) i < 256)
  | None => len = 0 /\ dat = []
  end.

Lemma stored_src_of_rt : forall s t buf len dat,
  lz_rel s t -> 0 <= len -> stored_src_rt t buf len dat -> stored_src s buf len dat.
Proof.
  intros s t buf len dat Hlz Hl Hsrc. destruct buf as [off|]; [|exact Hsrc].
  destruct Hsrc as (Ho & Hoe & -> & Hby). destruct Hlz as (Lw & _ & _ & Rw & _).
  unfold stored_src. rewrite Lw. split; [exact Ho|]. split; [exact Hoe|]. split.
  - rewrite (arr_rel_slice _ _ _ _ off len Rw) by lia. reflexivity.
  - unfold RD.win_take. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (k & <- & Hk).
    apply in_seq in Hk. apply Hby. lia.
Qed.

Lemma bw4_proj : forall s s', bw4 s s' ->
  DS.ds_pending_out s' = DS.ds_pending_out s /\ DS.ds_strm s' = DS.ds_strm s
  /\ DS.ds_window s' = DS.ds_window s /\ DS.ds_sym_next s' = DS.ds_sym_next s.
Proof. intros s s' (E & _). rewrite E. unfold set4. s5bw. repeat split. Qed.

Theorem pair_tr_stored_block : forall s t pre_out pre_in buf len last dat,
  dst_rel s t pre_out pre_in ->
  DS.ds_sym_next s = 0 ->
  DS.ds_pending_out s = 0 ->
  DS.ds_pending (DT.tr_stored_block s buf len last) <= arr_len (DS.ds_pending_buf s) ->
  0 <= len ->
  stored_src_rt t buf len dat ->
  dst_rel (DT.tr_stored_block s buf len last) (RD.setD_ts (RT.tr_stored_block dat len last (RD.d_ts t)) t)
          pre_out pre_in
  /\ DS.ds_pending_out (DT.tr_stored_block s buf len last) = 0
  /\ DS.ds_sym_next (DT.tr_stored_block s buf len last) = 0.
Proof.
  intros s t pre_out pre_in buf len last dat (Hg & Hlz & Hbw & Hsym & Htr & Hst) Hsn Hpo Hfin Hl Hsrc.
  pose proof (stored_src_of_rt s t buf len dat Hlz Hl Hsrc) as Hsrc5.
  pose proof (br_tr_stored_block s (RD.d_ts t) buf len last dat Hbw Hpo Hfin Hl Hsrc5) as Hbw'.
  pose proof (bw4_tr_stored_block s buf len last Hl) as F.
  pose proof (bw4_proj _ _ F) as (Epo & Est & Ew & Esn).
  revert Hbw' F Epo Est Ew Esn. generalize (DT.tr_stored_block s buf len last). intros s' Hbw' F Epo Est Ew Esn.
  destruct F as (E & Lpb & _ & _).
  split; [|split; congruence].
  unfold dst_rel. cbn [RD.d_ts RD.d_cfg RD.d_ls RD.d_strm RD.d_status RD.d_wrap RD.d_lastflush RD.setD_ts].
  split; [|split; [|split; [exact Hbw'|split; [|split]]]].
  - (* geom *)
    revert Hg. unfold geom_rel.
    cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.setD_ts].
    rewrite E. unfold set4. s5bw. rewrite Lpb. exact (fun H => H).
  - (* lz *)
    revert Hlz. unfold lz_rel. cbn [RD.d_ls RD.setD_ts].
    rewrite E. unfold set4. s5bw. exact (fun H => H).
  - (* sym: no symbol pending *)
    revert Hsym. unfold sym_rel. cbn [RD.d_ts RD.setD_ts].
    unfold RT.tr_stored_block. cbn [RT.ts_symnext RT.ts_symbuf RT.set_bw].
    rewrite E. unfold set4. s5bw. rewrite Lpb, Hsn.
    intros (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [intros i Hi; lia|].
    split; [exact H4 | intros Hc; lia].
  - (* trees *)
    revert Htr. unfold tree_rel. cbn [RD.d_ts RD.setD_ts].
    unfold RT.tr_stored_block.
    cbn [RT.ts_trees RT.ts_blcount RT.ts_heap RT.ts_depth RT.ts_maxcode RT.ts_heaplen RT.ts_heapmax
         RT.ts_optlen RT.ts_statlen RT.ts_matches RT.set_bw].
    rewrite E. unfold set4. s5bw. exact (fun H => H).
  - (* stream *)
    revert Hst. unfold strm_rel. cbn [RD.d_strm RD.setD_ts]. rewrite Est. exact (fun H => H).
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  The side conditions are needed                                        *)
(* ------------------------------------------------------------------------- *)

(** The bytes premise: a window value of 300 is copied as 300 by S5, while RT
    stores [u8 300 = 44]. *)
Definition s5_win300 : DS.deflate_state :=
  DS.set_window (DS.set_pending_buf s5_bw0 (arr_make 64 0)) (arr_set (arr_make 8 0) 0 300).

Example probe_bytes_needed :
  let s := DT.tr_stored_block s5_win300 (Some 0) 1 1 in
  arr_slice (DS.ds_pending_buf s) 0 (DS.ds_pending s)
  <> ZBitsOut.bw_out (RT.ts_bw (RT.tr_stored_block [300] 1 1 RT.ts_new)).
Proof. cbv zeta. vm_compute. discriminate. Qed.

(** The room premise: with a 6-byte buffer the copied byte falls past the end
    in S5 (dropped), while RT appends it. *)
Example probe_room_needed :
  let s0 := DS.set_window (DS.set_pending_buf s5_bw0 (arr_make 6 0)) (arr_make 8 7) in
  let s := DT.tr_stored_block s0 (Some 0) 2 1 in
  arr_slice (DS.ds_pending_buf s) 0 (DS.ds_pending s)
  <> ZBitsOut.bw_out (RT.ts_bw (RT.tr_stored_block [7; 7] 2 1 RT.ts_new)).
Proof. cbv zeta. vm_compute. discriminate. Qed.

Print Assumptions br_tr_stored_block.
Print Assumptions pair_tr_stored_block.
