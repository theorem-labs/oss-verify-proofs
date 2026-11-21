(** * Bridge.DEmit.BrZKit — byte writes and [flush_pending] at the level of [dst_rel].

    The zlib trailer ([DZTrailLive], the live-symbol case of pair D9) writes
    whole bytes into the pending queue ([putShortMSB]) and then flushes it.
    [dst_putShortMSB] relates the
    byte writes on both sides; [dst_flush_pending'] is [BrDFlush]'s
    [dst_flush_pending] without its empty-symbol-buffer premise: when
    symbols are live it asks that the queue (and the at most two bytes
    [bi_flush] adds) stay below the symbol area, which is all that zlib's
    overlay argument needs at the trailer. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz FlushBlockModel RefDeflSafeI2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrSendAll BrStored BrDFlush
  BrFbKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module I2 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI2.

(* ------------------------------------------------------------------------- *)
(* 1.  S5 frames                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma d_ts_setD_ts' : forall x t, RD.d_ts (RD.setD_ts x t) = x.
Proof. reflexivity. Qed.
Lemma ts_bw_set_bw' : forall b ts, RT.ts_bw (RT.set_bw b ts) = b.
Proof. reflexivity. Qed.
Lemma ts_symnext_set_bw' : forall b ts, RT.ts_symnext (RT.set_bw b ts) = RT.ts_symnext ts.
Proof. reflexivity. Qed.
Lemma ts_symbuf_set_bw' : forall b ts, RT.ts_symbuf (RT.set_bw b ts) = RT.ts_symbuf ts.
Proof. reflexivity. Qed.
Lemma trel_set_bw' : forall s ts b, trel s ts -> trel s (RT.set_bw b ts).
Proof. intros s ts b H. exact H. Qed.
Lemma gl_fields' : forall a b, gl_view a = gl_view b ->
  DS.ds_lit_bufsize a = DS.ds_lit_bufsize b /\ DS.ds_sym_end a = DS.ds_sym_end b.
Proof. intros a b E. unfold gl_view in E. injection E. intros. split; assumption. Qed.

Lemma gl_put_byte : forall s c, gl_view (DS.put_byte s c) = gl_view s.
Proof. intros s c. unfold DS.put_byte, gl_view. cbv zeta. autorewrite with s5f_pending s5f_pending_buf. reflexivity. Qed.

Lemma strm_put_byte : forall s c, DS.ds_strm (DS.put_byte s c) = DS.ds_strm s.
Proof. intros s c. unfold DS.put_byte. cbv zeta. autorewrite with s5f_pending s5f_pending_buf. reflexivity. Qed.

Lemma sym_next_put_byte : forall s c, DS.ds_sym_next (DS.put_byte s c) = DS.ds_sym_next s.
Proof. intros s c. unfold DS.put_byte. cbv zeta. autorewrite with s5f_pending s5f_pending_buf. reflexivity. Qed.

Lemma po_put_byte : forall s c, DS.ds_pending_out (DS.put_byte s c) = DS.ds_pending_out s.
Proof. intros s c. unfold DS.put_byte. cbv zeta. autorewrite with s5f_pending s5f_pending_buf. reflexivity. Qed.

Lemma fp_pb_eq : forall s, DS.ds_pending_buf (DL.flush_pending s) = DS.ds_pending_buf (DT.bi_flush s).
Proof.
  intros s. unfold DL.flush_pending, DT.tr_flush_bits. cbv zeta.
  generalize (DT.bi_flush s) as s1. intros s1.
  split_ifs; autorewrite with s5f_pending s5f_strm s5f_pending_out; reflexivity.
Qed.

(** [bi_flush] writes at most [pending_buf[pending]] and [pending_buf[pending + 1]]. *)
Lemma bi_flush_pb_frame : forall s j, DS.ds_pending s + 2 <= j ->
  arr_get (DS.ds_pending_buf (DT.bi_flush s)) j = arr_get (DS.ds_pending_buf s) j.
Proof.
  intros s j Hj. unfold DT.bi_flush, DT.put_short, DS.put_byte. cbv zeta.
  split_ifs; bw6_fields; rewrite ?arr_get_set_other by lia; reflexivity.
Qed.

(** The queue only shrinks, up to the at most two bytes [bi_flush] adds. *)
Lemma fp_sum : forall s, 0 <= DS.ds_pending s -> DS.ds_pending s + 2 < 2 ^ 32 -> 0 <= DS.ds_bi_valid s <= 16 ->
  0 <= DS.ds_pending_out s -> 0 <= DS.cs_avail_out (DS.ds_strm s) ->
  DS.ds_pending_out (DL.flush_pending s) + DS.ds_pending (DL.flush_pending s)
  <= DS.ds_pending_out s + DS.ds_pending s + 2.
Proof.
  intros s Hp Hp32 Hbv Hpo Hav. destruct (bi_flush_facts s Hbv) as (P1 & P2 & P3 & P4).
  unfold DL.flush_pending, DT.tr_flush_bits. cbv zeta.
  revert P1 P2 P3 P4. generalize (DT.bi_flush s) as s1. intros s1 P1 P2 P3 P4.
  assert (Hav1 : 0 <= DS.cs_avail_out (DS.ds_strm s1)) by (rewrite P3; exact Hav).
  rewrite (wrap32_id (DS.ds_pending s1)) by lia.
  destruct (Z.ltb_spec (DS.cs_avail_out (DS.ds_strm s1)) (DS.ds_pending s1)) as [Hlt|Hge].
  - destruct (Z.eqb_spec (DS.cs_avail_out (DS.ds_strm s1)) 0) as [E0|E0]; [lia|].
    autorewrite with s5f_pending s5f_strm s5f_pending_out.
    destruct (Z.eqb_spec (DS.ds_pending s1 - DS.cs_avail_out (DS.ds_strm s1)) 0); cbv iota;
      autorewrite with s5f_pending s5f_strm s5f_pending_out; lia.
  - destruct (Z.eqb_spec (DS.ds_pending s1) 0) as [E0|E0]; [lia|].
    autorewrite with s5f_pending s5f_strm s5f_pending_out.
    replace (DS.ds_pending s1 - DS.ds_pending s1) with 0 by lia. cbn [Z.eqb].
    autorewrite with s5f_pending s5f_strm s5f_pending_out. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  [putShortMSB] on both sides                                           *)
(* ------------------------------------------------------------------------- *)

Theorem dst_putShortMSB : forall s t pre_out pre_in b,
  dst_rel s t pre_out pre_in -> room s 2 ->
  (0 < DS.ds_sym_next s -> DS.ds_pending s + 2 <= DS.ds_lit_bufsize s) ->
  dst_rel (DL.putShortMSB s b) (RD.setD_ts (RD.putShortMSB b (RD.d_ts t)) t) pre_out pre_in
  /\ DS.ds_pending (DL.putShortMSB s b) = DS.ds_pending s + 2
  /\ DS.ds_pending_out (DL.putShortMSB s b) = 0.
Proof.
  intros s t pre_out pre_in b Hrel [Hpo Hroom] Hsym.
  pose proof Hrel as (Hg & Hl & Hb & Hs & Ht & Hm).
  unfold DL.putShortMSB. cbv zeta.
  set (c1 := Z.shiftr b 8). set (c2 := Z.land b 255).
  pose proof (pending_put_byte s c1) as N1. pose proof (pending_put_byte (DS.put_byte s c1) c2) as N2.
  pose proof (pblen_put_byte s c1) as L1. pose proof (pblen_put_byte (DS.put_byte s c1) c2) as L2.
  pose proof (po_put_byte s c1) as O1. pose proof (po_put_byte (DS.put_byte s c1) c2) as O2.
  split; [|split; [lia | congruence]].
  unfold dst_rel. split; [|split; [|split; [|split; [|split]]]].
  - destruct (gl_rel s (DS.put_byte (DS.put_byte s c1) c2) t (RD.setD_ts (RD.putShortMSB b (RD.d_ts t)) t)
                ltac:(rewrite !gl_put_byte; reflexivity) ltac:(rewrite L2, L1; reflexivity)
                eq_refl eq_refl eq_refl eq_refl eq_refl Hg Hl) as [G _]. exact G.
  - destruct (gl_rel s (DS.put_byte (DS.put_byte s c1) c2) t (RD.setD_ts (RD.putShortMSB b (RD.d_ts t)) t)
                ltac:(rewrite !gl_put_byte; reflexivity) ltac:(rewrite L2, L1; reflexivity)
                eq_refl eq_refl eq_refl eq_refl eq_refl Hg Hl) as [_ L]. exact L.
  - unfold RD.putShortMSB. rewrite d_ts_setD_ts', ts_bw_set_bw'.
    apply br_put_byte; [apply br_put_byte; [exact Hb | split; lia] | split; [rewrite O1; exact Hpo | lia]].
  - destruct Hs as (Hsn0 & Hsr & Hsb & Hsz & Hsp). unfold sym_rel. cbv zeta.
    rewrite d_ts_setD_ts'. unfold RD.putShortMSB. rewrite ts_symnext_set_bw', ts_symbuf_set_bw'.
    rewrite !sym_next_put_byte, L2, L1.
    assert (EL : DS.ds_lit_bufsize (DS.put_byte (DS.put_byte s c1) c2) = DS.ds_lit_bufsize s)
      by (exact (proj1 (gl_fields' _ _ (eq_trans (gl_put_byte _ c2) (gl_put_byte s c1))))).
    assert (EE : DS.ds_sym_end (DS.put_byte (DS.put_byte s c1) c2) = DS.ds_sym_end s)
      by (exact (proj2 (gl_fields' _ _ (eq_trans (gl_put_byte _ c2) (gl_put_byte s c1))))).
    assert (EL1 : DS.ds_lit_bufsize (DS.put_byte s c1) = DS.ds_lit_bufsize s)
      by (exact (proj1 (gl_fields' _ _ (gl_put_byte s c1)))).
    rewrite EL, EE.
    split; [exact Hsn0|]. split; [exact Hsr|].
    split; [|split; [exact Hsz | intros Hi; rewrite O2, O1, N2, N1; specialize (Hsym Hi); lia]].
    intros i Hi. assert (Hsy : DS.ds_pending s + 2 <= DS.ds_lit_bufsize s) by (apply Hsym; lia).
    rewrite I2.sym_buf_get_put_byte by (rewrite ?N1, ?EL1; lia).
    rewrite I2.sym_buf_get_put_byte by lia. apply Hsb. exact Hi.
  - apply tree_rel_trel. rewrite d_ts_setD_ts'. unfold RD.putShortMSB. apply trel_set_bw'.
    apply (trel_nbw s); [rewrite !nbw_put_byte; reflexivity | exact Ht].
  - unfold strm_rel in *. cbv zeta in *. rewrite !strm_put_byte. exact Hm.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  [flush_pending] with live symbols                                     *)
(* ------------------------------------------------------------------------- *)

Theorem dst_flush_pending' : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> DS.ds_pending_out s = 0 -> 0 <= DS.ds_bi_valid s <= 16 ->
  DS.ds_pending s + 2 < 2 ^ 32 ->
  (0 < DS.ds_sym_next s -> DS.ds_pending s + 2 <= DS.ds_lit_bufsize s) ->
  flush_room s -> fp_ok s ->
  dst_rel (DL.flush_pending s) (RD.flush_pending t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in Hrel Hpo0 Hbv Hp32 Hsym Hfr Hok.
  pose proof Hrel as (Hg & Hl & Hb & Hs & Ht & Hm).
  pose proof Hm as Hm'. unfold strm_rel in Hm'. cbv zeta in Hm'.
  destruct Hm' as (_ & _ & _ & _ & _ & _ & Hout & Hav & _ & Htot & _).
  destruct (br_flush_pending s t pre_out (conj Hb (conj Hout (conj Hav Htot))) Hfr Hok)
    as (Hb' & Hout' & Hav' & Htot').
  destruct (rt_flush_pending_frame t) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 &
                                          F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22).
  pose proof (flush_pending_pb_len s) as PL.
  destruct (flush_pending_strm_in s) as (S1 & S2 & S3 & S4 & S5' & S6).
  pose proof (fp_sum s ltac:(destruct Hb as ((_ & P & _) & _); exact P) Hp32 Hbv ltac:(lia) ltac:(destruct Hok as (A & _); exact A)) as SUM.
  unfold dst_rel. split; [|split; [|split; [|split; [|split]]]].
  - unfold geom_rel in *. cbv zeta in *. rewrite F1, F2, F3, F4, PL.
    rewrite flush_pending_shape. bw6_fields. exact Hg.
  - unfold lz_rel in *. cbv zeta in *. rewrite F5. rewrite flush_pending_shape. bw6_fields. exact Hl.
  - exact Hb'.
  - destruct Hs as (Hsn0 & Hsr & Hsb & Hsz & Hsp). unfold sym_rel. cbv zeta.
    rewrite F19, F18, PL. unfold DS.sym_buf_get.
    rewrite (flush_pending_shape s). bw6_fields.
    split; [exact Hsn0|]. split; [exact Hsr|].
    split; [|split; [exact Hsz | intros Hi; specialize (Hsym Hi); lia]].
    intros i Hi. rewrite fp_pb_eq, bi_flush_pb_frame by (specialize (Hsym ltac:(lia)); lia).
    apply Hsb. exact Hi.
  - unfold tree_rel in *. cbv zeta in *.
    rewrite F11, F12, F13, F14, F15, F16, F17, F20, F21, F22.
    rewrite flush_pending_shape. bw6_fields. exact Ht.
  - unfold strm_rel in *. cbv zeta in *.
    destruct Hm as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
    rewrite S1, S2, S3, S4, S5', S6, F6, F7, F8, F9, F10.
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
    repeat split; assumption.
Qed.

Print Assumptions dst_putShortMSB.
Print Assumptions dst_flush_pending'.
