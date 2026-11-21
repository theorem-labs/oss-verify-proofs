(** * Bridge.DEmit.BrStored — pair D24 of PAIRS.md: [_tr_stored_block], S5 vs RT.

    Both models send the 3-bit block header, byte-align ([bi_windup]), write
    [LEN] and [NLEN] and then the block's bytes.  S5 copies the bytes from its
    window into [pending_buf] at [pending] ([arr_blit]); RT appends the window
    bytes ([win_take]) to its queue.  The only room condition is S5's own
    [sto_ok] form, the final [pending] inside the array: every earlier write
    is below it.  The bit writer's steps are [BrBits]'s; what this file adds
    is the copy ([blit_slice]) and the frames ([nbw], [pending_out], the
    array length). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees FlushBlockModel SendModel RefDeflSafeE1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrSendAll.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module FBM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.FlushBlockModel.
Module SM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.SendModel.
Module E1 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE1.

(* ------------------------------------------------------------------------- *)
(* 1.  S5 frames of the bit writer's steps                                   *)
(* ------------------------------------------------------------------------- *)

Lemma pending_put_byte : forall s c, DS.ds_pending (DS.put_byte s c) = DS.ds_pending s + 1.
Proof. intros s c. unfold DS.put_byte. cbv zeta. autorewrite with s5f_pending s5f_pending_buf. reflexivity. Qed.

Lemma pblen_put_byte : forall s c, arr_len (DS.ds_pending_buf (DS.put_byte s c)) = arr_len (DS.ds_pending_buf s).
Proof.
  intros s c. unfold DS.put_byte. cbv zeta. autorewrite with s5f_pending s5f_pending_buf. apply arr_len_set.
Qed.

Lemma nbw_put_byte : forall s c, nbw (DS.put_byte s c) = nbw s.
Proof. intros s c. unfold DS.put_byte, nbw. cbv zeta. autorewrite with s5f_pending s5f_pending_buf. reflexivity. Qed.

Lemma pending_put_short : forall s w, DS.ds_pending (DT.put_short s w) = DS.ds_pending s + 2.
Proof. intros s w. unfold DT.put_short. cbv zeta. rewrite !pending_put_byte. lia. Qed.

Lemma pblen_put_short : forall s w, arr_len (DS.ds_pending_buf (DT.put_short s w)) = arr_len (DS.ds_pending_buf s).
Proof. intros s w. unfold DT.put_short. cbv zeta. rewrite !pblen_put_byte. reflexivity. Qed.

Lemma nbw_put_short : forall s w, nbw (DT.put_short s w) = nbw s.
Proof. intros s w. unfold DT.put_short. cbv zeta. rewrite !nbw_put_byte. reflexivity. Qed.

Lemma bi_windup_frame : forall s,
  DS.ds_pending s <= DS.ds_pending (DT.bi_windup s)
  /\ arr_len (DS.ds_pending_buf (DT.bi_windup s)) = arr_len (DS.ds_pending_buf s)
  /\ nbw (DT.bi_windup s) = nbw s.
Proof.
  intros s. unfold DT.bi_windup. cbv zeta.
  assert (F : forall y, DS.ds_pending (DS.set_bi_valid (DS.set_bi_buf y 0) 0) = DS.ds_pending y
     /\ arr_len (DS.ds_pending_buf (DS.set_bi_valid (DS.set_bi_buf y 0) 0)) = arr_len (DS.ds_pending_buf y)
     /\ nbw (DS.set_bi_valid (DS.set_bi_buf y 0) 0) = nbw y).
  { intros y. unfold nbw. autorewrite with s5f_bi_valid s5f_bi_buf. split; [reflexivity | split; reflexivity]. }
  destruct (8 <? DS.ds_bi_valid s); [|destruct (0 <? DS.ds_bi_valid s)];
    rewrite (proj1 (F _)), (proj1 (proj2 (F _))), (proj2 (proj2 (F _))).
  - rewrite pending_put_short, pblen_put_short, nbw_put_short. split; [lia | split; reflexivity].
  - rewrite pending_put_byte, pblen_put_byte, nbw_put_byte. split; [lia | split; reflexivity].
  - split; [lia | split; reflexivity].
Qed.

Lemma keeps_po : FBM.keeps DS.ds_pending_out true true.
Proof.
  constructor; intros; try match goal with t : DS.tree_id |- _ => destruct t end;
    match goal with s : DS.deflate_state |- _ => destruct s; reflexivity end.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The copy                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma slice_nat_app : forall {A} n m (a : parr A) ofs,
  arr_slice_nat a ofs (n + m) = arr_slice_nat a ofs n ++ arr_slice_nat a (ofs + Z.of_nat n) m.
Proof.
  induction n as [|n IH]; intros m a ofs; cbn [arr_slice_nat Nat.add app].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. replace (ofs + Z.of_nat (S n)) with (ofs + 1 + Z.of_nat n) by lia. reflexivity.
Qed.

Lemma slice_nat_ext : forall {A} n (a b : parr A) ofs,
  (forall j, ofs <= j < ofs + Z.of_nat n -> arr_get a j = arr_get b j) ->
  arr_slice_nat a ofs n = arr_slice_nat b ofs n.
Proof.
  induction n as [|n IH]; intros a b ofs H; cbn [arr_slice_nat]; [reflexivity|].
  rewrite (H ofs) by lia. rewrite (IH a b (ofs + 1)); [reflexivity|]. intros j Hj. apply H. lia.
Qed.

(** The queue after the copy: the old queue, then the window bytes. *)
Lemma blit_slice : forall (pb win : arr) (w : Base.zarr) p off len,
  0 <= p -> 0 <= off -> 0 <= len -> p + len <= arr_len pb ->
  (forall i, off <= i < off + len -> arr_get win i = w i /\ 0 <= w i < 256) ->
  arr_slice (arr_blit pb p win off len) 0 (p + len)
  = arr_slice pb 0 p ++ map Base.u8 (RD.win_take w off len).
Proof.
  intros pb win w p off len Hp Hoff Hlen Hroom Hw.
  unfold arr_slice. replace (Z.to_nat (p + len)) with (Z.to_nat p + Z.to_nat len)%nat by lia.
  rewrite slice_nat_app. f_equal.
  - apply slice_nat_ext. intros j Hj. rewrite arr_get_blit.
    replace (p <=? j) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - change (arr_slice_nat (arr_blit pb p win off len) (0 + Z.of_nat (Z.to_nat p)) (Z.to_nat len))
      with (arr_slice (arr_blit pb p win off len) (0 + Z.of_nat (Z.to_nat p)) len).
    replace (0 + Z.of_nat (Z.to_nat p)) with p by lia.
    rewrite (arr_rel_slice (arr_blit pb p win off len) (fun j => w (off + (j - p))) p (p + len) p len);
      [| | lia | lia | lia].
    + unfold RD.win_take. rewrite map_map. apply map_ext_in. intros k Hk. apply in_seq in Hk. cbv beta.
      replace (off + (p + Z.of_nat k - p)) with (off + Z.of_nat k) by lia.
      destruct (Hw (off + Z.of_nat k) ltac:(lia)) as [_ R]. unfold Base.u8. rewrite Z.mod_small by lia. reflexivity.
    + intros j Hj. rewrite arr_get_blit.
      destruct (Z.leb_spec p j); [|lia]. destruct (Z.ltb_spec j (p + Z.max 0 len)); [|lia].
      replace (arr_inb pb j) with true by (symmetry; apply arr_inb_spec; lia). cbn [andb].
      apply (Hw (off + (j - p))). lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The values                                                            *)
(* ------------------------------------------------------------------------- *)

Lemma bw_put_short_u16 : forall w b, ZBitsOut.bw_put_short (Base.u16 w) b = ZBitsOut.bw_put_short w b.
Proof.
  intros w b. unfold ZBitsOut.bw_put_short, ZBitsOut.bw_put_byte. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
  assert (E8 : Base.u8 (Base.u16 w) = Base.u8 w).
  { rewrite <- wrap16_u16, <- !wrap8_u8. unfold wrap8, wrap16. rewrite <- Z.land_assoc. reflexivity. }
  assert (E16 : Base.u16 (Base.u16 w) = Base.u16 w) by (unfold Base.u16; apply Z.mod_mod; lia).
  rewrite E8, E16. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The pair                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem br_tr_stored_block : forall s ts (w : Base.zarr) off len last,
  bw_rel s (RT.ts_bw ts) -> DS.ds_pending_out s = 0 -> 0 <= off -> 0 <= len ->
  (forall i, off <= i < off + len -> arr_get (DS.ds_window s) i = w i /\ 0 <= w i < 256) ->
  DS.ds_pending (DT.tr_stored_block s (Some off) len last) <= arr_len (DS.ds_pending_buf s) ->
  bw_rel (DT.tr_stored_block s (Some off) len last) (RT.ts_bw (RT.tr_stored_block (RD.win_take w off len) len last ts))
  /\ DS.ds_pending_out (DT.tr_stored_block s (Some off) len last) = 0
  /\ arr_len (DS.ds_pending_buf (DT.tr_stored_block s (Some off) len last)) = arr_len (DS.ds_pending_buf s)
  /\ nbw (DT.tr_stored_block s (Some off) len last) = nbw s.
Proof.
  intros s ts w off len last Hb Hpo Hoff Hlen Hw Hfin.
  unfold DT.tr_stored_block in *. unfold RT.tr_stored_block. cbv beta iota zeta in *.
  cbn [RT.ts_bw RT.set_bw].
  change RT.STORED_BLOCK with DS.STORED_BLOCK.
  set (v0 := Z.shiftl DS.STORED_BLOCK 1 + last) in *.
  set (b := RT.ts_bw ts) in *.
  set (s1 := DT.send_bits s v0 3) in *.
  set (s2 := DT.bi_windup s1) in *.
  set (s3 := DT.put_short s2 (wrap16 len)) in *.
  set (s4 := DT.put_short s3 (wrap16 (Z.lnot len))) in *.
  (* frames *)
  pose proof (E1.send_bits_pending_mono s v0 3) as P1. fold s1 in P1.
  destruct (bi_windup_frame s1) as (P2 & L2 & N2). fold s2 in P2, L2, N2.
  pose proof (pending_put_short s2 (wrap16 len)) as P3. fold s3 in P3.
  pose proof (pending_put_short s3 (wrap16 (Z.lnot len))) as P4. fold s4 in P4.
  assert (L1 : arr_len (DS.ds_pending_buf s1) = arr_len (DS.ds_pending_buf s)) by apply SM.sb_pbl.
  assert (L4 : arr_len (DS.ds_pending_buf s4) = arr_len (DS.ds_pending_buf s)).
  { subst s4 s3. rewrite !pblen_put_short, L2, L1. reflexivity. }
  assert (N4 : nbw s4 = nbw s).
  { subst s4 s3. rewrite !nbw_put_short, N2. subst s1. apply nbw_send_bits. }
  assert (O4 : DS.ds_pending_out s4 = 0).
  { subst s4 s3 s2 s1. rewrite (FBM.k_put_short _ _ _ keeps_po eq_refl), (FBM.k_put_short _ _ _ keeps_po eq_refl),
      (FBM.k_bi_windup _ _ _ keeps_po eq_refl), (FBM.k_send_bits _ _ _ keeps_po eq_refl). exact Hpo. }
  assert (W4 : DS.ds_window s4 = DS.ds_window s).
  { subst s4 s3 s2 s1. rewrite (FBM.k_put_short _ _ _ FBM.keeps_window eq_refl),
      (FBM.k_put_short _ _ _ FBM.keeps_window eq_refl), (FBM.k_bi_windup _ _ _ FBM.keeps_window eq_refl),
      (FBM.k_send_bits _ _ _ FBM.keeps_window eq_refl). reflexivity. }
  assert (O1 : DS.ds_pending_out s1 = 0) by (subst s1; rewrite (FBM.k_send_bits _ _ _ keeps_po eq_refl); exact Hpo).
  assert (O2 : DS.ds_pending_out s2 = 0) by (subst s2; rewrite (FBM.k_bi_windup _ _ _ keeps_po eq_refl); exact O1).
  assert (O3 : DS.ds_pending_out s3 = 0) by (subst s3; rewrite (FBM.k_put_short _ _ _ keeps_po eq_refl); exact O2).
  assert (L3 : arr_len (DS.ds_pending_buf s3) = arr_len (DS.ds_pending_buf s2)) by (subst s3; apply pblen_put_short).
  (* the final pending *)
  assert (Hfin' : DS.ds_pending s4 + len <= arr_len (DS.ds_pending_buf s)).
  { revert Hfin. destruct (negb (len =? 0)); intros Hfin; autorewrite with s5f_pending s5f_pending_buf in Hfin; exact Hfin. }
  (* the bit writer's steps *)
  assert (B1 : bw_rel s1 (ZBitsOut.bw_send_bits v0 3 b)) by (apply br_send_bits; [exact Hb | split; lia]).
  assert (B2 : bw_rel s2 (ZBitsOut.bw_windup (ZBitsOut.bw_send_bits v0 3 b)))
    by (apply br_bi_windup; [exact B1 | split; lia]).
  assert (B3 : bw_rel s3 (ZBitsOut.bw_put_short len (ZBitsOut.bw_windup (ZBitsOut.bw_send_bits v0 3 b)))).
  { rewrite <- bw_put_short_u16, <- wrap16_u16. apply br_put_short; [exact B2 | split; lia]. }
  assert (B4 : bw_rel s4 (ZBitsOut.bw_put_short (Base.u16 (- len - 1))
                           (ZBitsOut.bw_put_short len (ZBitsOut.bw_windup (ZBitsOut.bw_send_bits v0 3 b))))).
  { rewrite bw_put_short_u16. replace (- len - 1) with (Z.lnot len) by (unfold Z.lnot; lia).
    rewrite <- bw_put_short_u16, <- wrap16_u16. apply br_put_short; [exact B3 | split; lia]. }
  set (b4 := ZBitsOut.bw_put_short (Base.u16 (- len - 1))
               (ZBitsOut.bw_put_short len (ZBitsOut.bw_windup (ZBitsOut.bw_send_bits v0 3 b)))) in *.
  clearbody b4.
  destruct B4 as ((R1 & R2 & R3 & R4) & R5 & R6).
  rewrite O4 in R1, R3, R4.
  unfold bw_rel, pend_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
  destruct (Z.eqb_spec len 0) as [L0|L0]; cbn [negb].
  - subst len. cbn [RD.win_take seq map Z.to_nat]. rewrite app_nil_r.
    autorewrite with s5f_pending. rewrite Z.add_0_r, O4.
    refine (conj (conj (conj _ (conj _ (conj _ _))) (conj _ _)) (conj _ (conj _ _))).
    + lia.
    + lia.
    + lia.
    + exact R4.
    + exact R5.
    + exact R6.
    + reflexivity.
    + exact L4.
    + unfold nbw in *. autorewrite with s5f_pending. exact N4.
  - autorewrite with s5f_pending s5f_pending_buf. rewrite O4.
    refine (conj (conj (conj _ (conj _ (conj _ _))) (conj _ _)) (conj _ (conj _ _))).
    + lia.
    + lia.
    + rewrite arr_len_blit, L4. lia.
    + rewrite W4. rewrite (blit_slice _ _ w); [| lia | exact Hoff | exact Hlen | rewrite L4; lia | exact Hw].
      rewrite R4. reflexivity.
    + exact R5.
    + exact R6.
    + reflexivity.
    + rewrite arr_len_blit. exact L4.
    + unfold nbw in *. autorewrite with s5f_pending s5f_pending_buf. exact N4.
Qed.

Print Assumptions br_tr_stored_block.
