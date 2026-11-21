(** * Bridge.DMatch.MReadBuf — group M: pair D17a, [read_buf], S5 vs RT.

    S5's [read_buf] ([Z/DeflateLz.v:73]) copies [len = min size avail_in]
    bytes from the call's input array at [next_in], either into the window at
    an offset ([RB_window off]) or onto the call's output ([RB_next_out]),
    updates the Adler-32 check, and advances [next_in] / [total_in].  RT's
    ([Spec/PngModel/Deflate.v:287]) returns the bytes and moves them from the
    unread list to the consumed list; its callers blit them into the window
    ([fw_step], [dst_tail]) or append them to [zs_out] ([dst_step]).

    The premises are the stream ones only: no checksum other than Adler-32
    ([rb_ok]: wrap 0 or 1), [total_in] does not wrap, and a window write fits
    S5's window (S5 drops a write past its end, RT's closure does not). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrAdler BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

(* ------------------------------------------------------------------------- *)
(* 1.  Slice kit                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma m_slice_nat_app : forall {A} n m (a : parr A) o,
  arr_slice_nat a o n ++ arr_slice_nat a (o + Z.of_nat n) m = arr_slice_nat a o (n + m).
Proof.
  induction n as [|n IH]; intros m a o.
  - cbn [arr_slice_nat app Nat.add]. rewrite Z.add_0_r. reflexivity.
  - cbn [arr_slice_nat app Nat.add]. f_equal.
    replace (o + Z.of_nat (S n)) with ((o + 1) + Z.of_nat n) by lia. apply IH.
Qed.

Lemma m_slice_app : forall (a : arr) o n m, 0 <= n -> 0 <= m ->
  arr_slice a o n ++ arr_slice a (o + n) m = arr_slice a o (n + m).
Proof.
  intros a o n m Hn Hm. unfold arr_slice.
  replace (Z.to_nat (n + m)) with (Z.to_nat n + Z.to_nat m)%nat by lia.
  rewrite <- m_slice_nat_app. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma m_slice_in : forall (a : arr) o n b,
  In b (arr_slice a o n) -> exists k, 0 <= k < n /\ b = arr_get a (o + k).
Proof.
  intros a o n b H. unfold arr_slice in H.
  apply In_nth with (d := 0) in H. destruct H as (k & Hk & Hb).
  rewrite arr_slice_nat_length in Hk. rewrite arr_slice_nat_nth in Hb by exact Hk.
  exists (Z.of_nat k). split; [lia | symmetry; exact Hb].
Qed.

Lemma m_slice_bytes : forall (a : arr) o n,
  (forall i, 0 <= i < arr_len a -> 0 <= arr_get a i < 256) ->
  0 <= o -> o + n <= arr_len a -> bytes (arr_slice a o n).
Proof.
  intros a o n Ha Ho Hn b Hb. apply m_slice_in in Hb as (k & Hk & ->). apply Ha. lia.
Qed.

Lemma m_map_u8_bytes : forall l, bytes l -> map Base.u8 l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [map]. rewrite Base.u8_id by (apply H; left; reflexivity).
  rewrite IH by (intros b Hb; apply H; right; exact Hb). reflexivity.
Qed.

Lemma m_zlen_slice : forall (a : arr) o n, 0 <= n -> Chunk.zlen (arr_slice a o n) = n.
Proof. intros a o n Hn. change Chunk.zlen with (@zlength Z). rewrite arr_slice_length. lia. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The two models' read_buf, as equations                                *)
(* ------------------------------------------------------------------------- *)

Definition s5_rb_strm (st : DS.cstrm) (wrap len : Z) (out : list Z) : DS.cstrm :=
  let bytes := arr_slice (DS.cs_input st) (DS.cs_next_in st) len in
  let st1 := DS.cset_out_rev (DS.cset_avail_in st (DS.cs_avail_in st - len))
                             (List.rev_append out (DS.cs_out_rev st)) in
  let st2 := if Z.eqb wrap 1 then DS.cset_adler st1 (SLz.adler32_upd (DS.cs_adler st1) bytes)
             else if Z.eqb wrap 2 then DS.cset_adler st1 (SLz.crc32_upd (DS.cs_adler st1) bytes)
             else st1 in
  DS.cset_total_in (DS.cset_next_in st2 (DS.cs_next_in st2 + len))
                   (wrap64 (DS.cs_total_in st2 + len)).

(** The common shape of every RT read_buf result. *)
Lemma m_rt_read_buf_eq : forall wrap size st,
  let len := Z.min size (Chunk.zlen (RD.zs_in st)) in
  len <> 0 ->
  RD.read_buf wrap size st
  = (map Base.u8 (firstn (Z.to_nat len) (RD.zs_in st)),
     RD.setZ_totalin (RD.zs_totalin st + len)
       (RD.setZ_adler (if Z.eqb wrap 1
                       then Checksum.adler32_z (RD.zs_adler st) false
                              (map Base.u8 (firstn (Z.to_nat len) (RD.zs_in st)))
                       else if Z.eqb wrap 2
                       then Checksum.crc32_z_at (RD.zs_adler st) 0
                              (map Base.u8 (firstn (Z.to_nat len) (RD.zs_in st)))
                       else RD.zs_adler st)
         (RD.setZ_done (RD.zs_done st ++ map Base.u8 (firstn (Z.to_nat len) (RD.zs_in st)))
           (RD.setZ_in (skipn (Z.to_nat len) (RD.zs_in st)) st)))).
Proof.
  intros wrap size st len Hl. unfold RD.read_buf. cbv zeta.
  replace (if size <? Chunk.zlen (RD.zs_in st) then size else Chunk.zlen (RD.zs_in st)) with len
    by (subst len; destruct (Z.ltb_spec size (Chunk.zlen (RD.zs_in st))); lia).
  destruct (Z.eqb_spec len 0); [contradiction|]. reflexivity.
Qed.

Lemma m_rt_read_buf_zero : forall wrap size st,
  Z.min size (Chunk.zlen (RD.zs_in st)) = 0 -> RD.read_buf wrap size st = ([], st).
Proof.
  intros wrap size st Hl. unfold RD.read_buf. cbv zeta.
  replace (if size <? Chunk.zlen (RD.zs_in st) then size else Chunk.zlen (RD.zs_in st)) with 0
    by (destruct (Z.ltb_spec size (Chunk.zlen (RD.zs_in st))); lia).
  reflexivity.
Qed.

Lemma m_s5_read_buf_window_eq : forall s off size,
  let len := Z.min size (DS.cs_avail_in (DS.ds_strm s)) in
  len <> 0 ->
  SLz.read_buf s (SLz.RB_window off) size
  = (DS.set_strm (DS.set_window s (arr_upd (DS.ds_window s) off
                     (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) len)))
                 (s5_rb_strm (DS.ds_strm s) (DS.ds_wrap s) len []), len).
Proof.
  intros s off size len Hl. unfold SLz.read_buf. cbv zeta.
  replace (if size <? DS.cs_avail_in (DS.ds_strm s) then size else DS.cs_avail_in (DS.ds_strm s)) with len
    by (subst len; destruct (Z.ltb_spec size (DS.cs_avail_in (DS.ds_strm s))); lia).
  destruct (Z.eqb_spec len 0); [contradiction|].
  cbv beta iota. unfold s5_rb_strm. cbv zeta.
  rewrite ds_wrap__set_window.
  (* the S5 code builds the out_rev field unchanged: rev_append [] l = l *)
  destruct (DS.ds_wrap s =? 1); [|destruct (DS.ds_wrap s =? 2)]; reflexivity.
Qed.

Lemma m_s5_read_buf_next_out_eq : forall s size,
  let len := Z.min size (DS.cs_avail_in (DS.ds_strm s)) in
  len <> 0 ->
  SLz.read_buf s SLz.RB_next_out size
  = (DS.set_strm s (s5_rb_strm (DS.ds_strm s) (DS.ds_wrap s) len
                     (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) len)), len).
Proof.
  intros s size len Hl. unfold SLz.read_buf. cbv zeta.
  replace (if size <? DS.cs_avail_in (DS.ds_strm s) then size else DS.cs_avail_in (DS.ds_strm s)) with len
    by (subst len; destruct (Z.ltb_spec size (DS.cs_avail_in (DS.ds_strm s))); lia).
  destruct (Z.eqb_spec len 0); [contradiction|].
  cbv beta iota. unfold s5_rb_strm, DS.cs_emit. cbv zeta.
  destruct (DS.ds_wrap s =? 1); [|destruct (DS.ds_wrap s =? 2)]; reflexivity.
Qed.

Lemma m_s5_read_buf_zero : forall s dst size,
  Z.min size (DS.cs_avail_in (DS.ds_strm s)) = 0 -> SLz.read_buf s dst size = (s, 0).
Proof.
  intros s dst size Hl. unfold SLz.read_buf. cbv zeta.
  replace (if size <? DS.cs_avail_in (DS.ds_strm s) then size else DS.cs_avail_in (DS.ds_strm s)) with 0
    by (destruct (Z.ltb_spec size (DS.cs_avail_in (DS.ds_strm s))); lia).
  reflexivity.
Qed.

Lemma m_s5_rb_strm_fields : forall st w len out,
  DS.cs_input (s5_rb_strm st w len out) = DS.cs_input st
  /\ DS.cs_next_in (s5_rb_strm st w len out) = DS.cs_next_in st + len
  /\ DS.cs_avail_in (s5_rb_strm st w len out) = DS.cs_avail_in st - len
  /\ DS.cs_out_rev (s5_rb_strm st w len out) = List.rev_append out (DS.cs_out_rev st)
  /\ DS.cs_avail_out (s5_rb_strm st w len out) = DS.cs_avail_out st
  /\ DS.cs_total_in (s5_rb_strm st w len out) = wrap64 (DS.cs_total_in st + len)
  /\ DS.cs_total_out (s5_rb_strm st w len out) = DS.cs_total_out st
  /\ DS.cs_data_type (s5_rb_strm st w len out) = DS.cs_data_type st
  /\ DS.cs_adler (s5_rb_strm st w len out)
     = (if Z.eqb w 1 then SLz.adler32_upd (DS.cs_adler st) (arr_slice (DS.cs_input st) (DS.cs_next_in st) len)
        else if Z.eqb w 2 then SLz.crc32_upd (DS.cs_adler st) (arr_slice (DS.cs_input st) (DS.cs_next_in st) len)
        else DS.cs_adler st).
Proof.
  intros st w len out. unfold s5_rb_strm. cbv zeta.
  destruct (Z.eqb w 1); [|destruct (Z.eqb w 2)]; repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The stream half                                                       *)
(* ------------------------------------------------------------------------- *)

(** After moving [len] bytes, the stream relation holds again with [out]
    appended on the S5 side and [outR] on the RT side. *)
Lemma m_rb_strm_rel : forall s t pre_out pre_in len out outR,
  strm_rel s t pre_out pre_in -> rb_ok t -> DS.ds_wrap s = RD.d_wrap t ->
  0 < len <= DS.cs_avail_in (DS.ds_strm s) ->
  RD.zs_out (RD.d_strm t) ++ outR = pre_out ++ DS.cs_output (DS.ds_strm s) ++ out ->
  let dat := map Base.u8 (firstn (Z.to_nat len) (RD.zs_in (RD.d_strm t))) in
  let z := RD.d_strm t in
  strm_rel (DS.set_strm s (s5_rb_strm (DS.ds_strm s) (DS.ds_wrap s) len out))
    (RD.setD_strm
       (RD.setZ_out (RD.zs_out z ++ outR)
         (RD.setZ_totalin (RD.zs_totalin z + len)
           (RD.setZ_adler (if Z.eqb (RD.d_wrap t) 1
                           then Checksum.adler32_z (RD.zs_adler z) false dat
                           else if Z.eqb (RD.d_wrap t) 2
                           then Checksum.crc32_z_at (RD.zs_adler z) 0 dat
                           else RD.zs_adler z)
             (RD.setZ_done (RD.zs_done z ++ dat)
               (RD.setZ_in (skipn (Z.to_nat len) (RD.zs_in z)) z))))) t)
    pre_out pre_in
  /\ dat = arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) len.
Proof.
  intros s t po pi len out outR Hst Hrb Hw Hlen Hout dat z.
  unfold strm_rel in Hst. cbv zeta in Hst.
  destruct Hst as (Hni & Hai & Hfit & Hby & Hin & Hdone & Hzo & Hao & Hti & Hto & Had & Hdt).
  destruct Hrb as (Hwr & Hti0 & Hti64).
  fold z in Hti0, Hti64, Hin, Hdone, Hzo, Hao, Hti, Hto, Had, Hdt, Hout.
  set (st := DS.ds_strm s) in *.
  assert (Hzl : Chunk.zlen (RD.zs_in z) = DS.cs_avail_in st)
    by (subst z; rewrite <- Hin; apply m_zlen_slice; lia).
  assert (Hdat : dat = arr_slice (DS.cs_input st) (DS.cs_next_in st) len).
  { subst dat z. rewrite <- Hin. rewrite <- slice_firstn by lia.
    apply m_map_u8_bytes, m_slice_bytes; [exact Hby | lia | lia]. }
  split; [|exact Hdat].
  assert (Hbytes : bytes (arr_slice (DS.cs_input st) (DS.cs_next_in st) len))
    by (apply m_slice_bytes; [exact Hby | lia | lia]).
  destruct (m_s5_rb_strm_fields st (DS.ds_wrap s) len out)
    as (HA1 & HA2 & HA3 & HA4 & HA5 & HA6 & HA7 & HA8 & HA9).
  assert (HAd : DS.cs_adler (s5_rb_strm st (DS.ds_wrap s) len out)
                = (if Z.eqb (RD.d_wrap t) 1
                   then Checksum.adler32_z (RD.zs_adler z) false dat
                   else if Z.eqb (RD.d_wrap t) 2
                   then Checksum.crc32_z_at (RD.zs_adler z) 0 dat
                   else RD.zs_adler z)).
  { rewrite HA9, Hw. destruct Hwr as [W|W]; rewrite W; cbn [Z.eqb Pos.eqb].
    - symmetry. exact Had.
    - rewrite Hdat, Had. apply br_adler32_upd. exact Hbytes. }
  unfold strm_rel. cbv zeta.
  autorewrite with s5f_strm.
  cbn [RD.d_strm RD.setD_strm RD.setZ_out RD.setZ_totalin RD.setZ_adler RD.setZ_done RD.setZ_in
       RD.zs_in RD.zs_done RD.zs_out RD.zs_availout RD.zs_totalin RD.zs_totalout RD.zs_adler
       RD.zs_datatype].
  fold z.
  unfold DS.cs_output.
  rewrite HA1, HA2, HA3, HA4, HA5, HA6, HA7, HA8, HAd.
  rewrite wrap64_id by (rewrite <- Hti; mpow; lia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hby|].
  split; [rewrite <- Hin; rewrite <- slice_skipn by lia; f_equal; lia|].
  split; [rewrite Hdone, Hdat, <- app_assoc; f_equal; apply m_slice_app; lia|].
  split.
  { rewrite Hout. unfold DS.cs_output. rewrite !rev_append_rev, !app_nil_r, rev_app_distr, rev_involutive.
    rewrite app_assoc. reflexivity. }
  split; [exact Hao|]. split; [rewrite Hti; reflexivity|]. split; [exact Hto|].
  split; [reflexivity|exact Hdt].
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The pairs                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma m_rb_rb_ok : forall t size,
  rb_ok t -> 0 <= size ->
  rb_ok (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t))) t).
Proof.
  intros t size (Hw & H0 & H64) Hsz.
  destruct (Z.eq_dec (Z.min size (Chunk.zlen (RD.zs_in (RD.d_strm t)))) 0) as [E|E].
  - rewrite m_rt_read_buf_zero by exact E. cbn [snd]. exact (conj Hw (conj H0 H64)).
  - rewrite m_rt_read_buf_eq by exact E. cbn [snd]. unfold rb_ok.
    cbn [RD.d_strm RD.d_wrap RD.setD_strm RD.setZ_totalin RD.setZ_adler RD.setZ_done RD.setZ_in
         RD.zs_in RD.zs_totalin].
    assert (Hz : 0 <= Chunk.zlen (RD.zs_in (RD.d_strm t))) by (unfold Chunk.zlen; lia).
    assert (Hk : Chunk.zlen (skipn (Z.to_nat (Z.min size (Chunk.zlen (RD.zs_in (RD.d_strm t)))))
                                   (RD.zs_in (RD.d_strm t)))
                 = Chunk.zlen (RD.zs_in (RD.d_strm t)) - Z.min size (Chunk.zlen (RD.zs_in (RD.d_strm t)))).
    { unfold Chunk.zlen. rewrite length_skipn. lia. }
    rewrite Hk. split; [exact Hw|]. mpow; lia.
Qed.

Theorem m_read_buf_window : forall s t pre_out pre_in off size,
  dst_rel s t pre_out pre_in -> rb_ok t -> 0 <= size -> 0 <= off ->
  off + Z.min size (Chunk.zlen (RD.zs_in (RD.d_strm t))) <= RD.ls_windowsize (RD.d_ls t) ->
  snd (SLz.read_buf s (SLz.RB_window off) size)
    = Chunk.zlen (fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
  /\ dst_rel (fst (SLz.read_buf s (SLz.RB_window off) size))
       (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
          (RD.setD_ls (RD.setL_window
                         (RD.win_blit (fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t))) off
                                      (RD.ls_window (RD.d_ls t)))
                         (RD.d_ls t)) t))
       pre_out pre_in
  /\ rb_ok (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t))) t).
Proof.
  intros s t po pi off size Hrel Hrb Hsz Hoff Hfit.
  split; [|split]; [| |apply m_rb_rb_ok; assumption].
  all: destruct Hrel as (Hg & Hl & Hbw & Hsy & Htr & Hst).
  all: pose proof Hst as Hst'; unfold strm_rel in Hst'; cbv zeta in Hst';
       destruct Hst' as (Hni & Hai & Hfitin & Hby & Hin & _).
  all: assert (Hzl : Chunk.zlen (RD.zs_in (RD.d_strm t)) = DS.cs_avail_in (DS.ds_strm s))
         by (rewrite <- Hin; apply m_zlen_slice; lia).
  all: rewrite Hzl in *.
  all: assert (Hw : DS.ds_wrap s = RD.d_wrap t) by (unfold geom_rel in Hg; cbv zeta in Hg; tauto).
  all: destruct (Z.eq_dec (Z.min size (DS.cs_avail_in (DS.ds_strm s))) 0) as [E|E].
  - rewrite m_s5_read_buf_zero by exact E. rewrite m_rt_read_buf_zero by (rewrite Hzl; exact E).
    reflexivity.
  - rewrite m_s5_read_buf_window_eq by exact E. rewrite m_rt_read_buf_eq by (rewrite Hzl; exact E).
    cbn [fst snd]. rewrite Hzl. unfold Chunk.zlen. rewrite length_map, length_firstn.
    unfold Chunk.zlen in Hzl. lia.
  - rewrite m_s5_read_buf_zero by exact E. rewrite m_rt_read_buf_zero by (rewrite Hzl; exact E).
    cbn [fst snd].
    (* RT reads the same window through [win_blit [] off] *)
    unfold dst_rel. split; [exact Hg|]. split; [|split; [exact Hbw|split; [exact Hsy|split; [exact Htr|exact Hst]]]].
    unfold lz_rel in *. cbv zeta in *.
    cbn [RD.d_ls RD.setD_ls RD.setD_strm RD.setL_window RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh
         RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch RD.ls_matchavail RD.ls_strstart RD.ls_matchstart
         RD.ls_lookahead RD.ls_prevlen RD.ls_insert RD.ls_highwater RD.ls_windowsize].
    destruct Hl as (H1 & H2 & H3 & H4 & Hrest).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact Hrest].
    intros i Hi. rewrite H4 by exact Hi. unfold RD.win_blit. cbv zeta.
    change (Chunk.zlen []) with 0. rewrite Z.add_0_r.
    destruct (Z.leb off i && Z.ltb i off) eqn:Ei; [|reflexivity].
    apply andb_prop in Ei as [Ea Eb]. apply Z.leb_le in Ea. apply Z.ltb_lt in Eb. lia.
  - rewrite m_s5_read_buf_window_eq by exact E.
    pose proof (m_rt_read_buf_eq (RD.d_wrap t) size (RD.d_strm t)) as ER. cbv zeta in ER.
    rewrite Hzl in ER. rewrite ER by exact E. clear ER.
    cbn [fst snd].
    set (len := Z.min size (DS.cs_avail_in (DS.ds_strm s))) in *.
    assert (Hlen : 0 < len <= DS.cs_avail_in (DS.ds_strm s)) by (subst len; lia).
    destruct (m_rb_strm_rel s t po pi len [] [] Hst Hrb Hw Hlen) as [Hst2 Hdat].
    { rewrite !app_nil_r. unfold strm_rel in Hst; cbv zeta in Hst; tauto. }
    cbv zeta in Hst2, Hdat.
    rewrite app_nil_r in Hst2.
    set (dat := map Base.u8 (firstn (Z.to_nat len) (RD.zs_in (RD.d_strm t)))) in *.
    unfold dst_rel. split; [exact Hg|]. split; [|split; [exact Hbw|split; [exact Hsy|split; [exact Htr|]]]].
    + unfold lz_rel in *. cbv zeta in *.
      autorewrite with s5f_strm s5f_window.
      cbn [RD.d_ls RD.setD_ls RD.setD_strm RD.setL_window RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh
           RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch RD.ls_matchavail RD.ls_strstart RD.ls_matchstart
           RD.ls_lookahead RD.ls_prevlen RD.ls_insert RD.ls_highwater RD.ls_windowsize].
      destruct Hl as (H1 & H2 & H3 & H4 & Hrest).
      split; [rewrite arr_len_upd; exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact Hrest].
      intros i Hi. rewrite (arr_get_upd _ _ _ _ 0). unfold RD.win_blit. cbv zeta.
      rewrite <- Hdat.
      assert (Hdl : zlength dat = len).
      { subst dat. unfold zlength. rewrite length_map, length_firstn. unfold Chunk.zlen in Hzl. lia. }
      change Chunk.zlen with (@zlength Z). rewrite Hdl.
      unfold arr_inb. rewrite H1.
      destruct (Z.leb_spec off i); destruct (Z.ltb_spec i (off + len));
        destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (RD.ls_windowsize (RD.d_ls t)));
        cbn [andb]; try lia; try (apply H4; exact Hi).
      unfold Base.zlist. reflexivity.
    + (* sym_rel, bw_rel, tree_rel above are about untouched fields; the stream: *)
      exact Hst2.
Qed.

Theorem m_read_buf_next_out : forall s t pre_out pre_in size,
  dst_rel s t pre_out pre_in -> rb_ok t -> 0 <= size ->
  snd (SLz.read_buf s SLz.RB_next_out size)
    = Chunk.zlen (fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
  /\ dst_rel (fst (SLz.read_buf s SLz.RB_next_out size))
       (RD.setD_strm (RD.setZ_out (RD.zs_out (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
                                   ++ fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
                                  (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))) t)
       pre_out pre_in
  /\ rb_ok (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t))) t).
Proof.
  intros s t po pi size Hrel Hrb Hsz.
  split; [|split]; [| |apply m_rb_rb_ok; assumption].
  all: destruct Hrel as (Hg & Hl & Hbw & Hsy & Htr & Hst).
  all: pose proof Hst as Hst'; unfold strm_rel in Hst'; cbv zeta in Hst';
       destruct Hst' as (Hni & Hai & Hfitin & Hby & Hin & Hdone & Hzo & _).
  all: assert (Hzl : Chunk.zlen (RD.zs_in (RD.d_strm t)) = DS.cs_avail_in (DS.ds_strm s))
         by (rewrite <- Hin; apply m_zlen_slice; lia).
  all: assert (Hw : DS.ds_wrap s = RD.d_wrap t) by (unfold geom_rel in Hg; cbv zeta in Hg; tauto).
  all: destruct (Z.eq_dec (Z.min size (DS.cs_avail_in (DS.ds_strm s))) 0) as [E|E].
  - rewrite m_s5_read_buf_zero by exact E. rewrite m_rt_read_buf_zero by (rewrite Hzl; exact E).
    reflexivity.
  - rewrite m_s5_read_buf_next_out_eq by exact E. rewrite m_rt_read_buf_eq by (rewrite Hzl; exact E).
    cbn [fst snd]. rewrite Hzl. unfold Chunk.zlen. rewrite length_map, length_firstn.
    unfold Chunk.zlen in Hzl. lia.
  - rewrite m_s5_read_buf_zero by exact E. rewrite m_rt_read_buf_zero by (rewrite Hzl; exact E).
    cbn [fst snd]. rewrite app_nil_r.
    replace (RD.setD_strm (RD.setZ_out (RD.zs_out (RD.d_strm t)) (RD.d_strm t)) t) with t
      by (destruct t as [? ? ? ? ? ? []]; reflexivity).
    exact (conj Hg (conj Hl (conj Hbw (conj Hsy (conj Htr Hst))))).
  - rewrite m_s5_read_buf_next_out_eq by exact E.
    pose proof (m_rt_read_buf_eq (RD.d_wrap t) size (RD.d_strm t)) as ER. cbv zeta in ER.
    rewrite Hzl in ER. rewrite ER by exact E. clear ER.
    cbn [fst snd].
    set (len := Z.min size (DS.cs_avail_in (DS.ds_strm s))) in *.
    assert (Hlen : 0 < len <= DS.cs_avail_in (DS.ds_strm s)) by (subst len; lia).
    set (dat := map Base.u8 (firstn (Z.to_nat len) (RD.zs_in (RD.d_strm t)))) in *.
    assert (Hdat : dat = arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) len).
    { subst dat. rewrite <- Hin. rewrite <- slice_firstn by lia.
      apply m_map_u8_bytes, m_slice_bytes; [exact Hby | lia | lia]. }
    destruct (m_rb_strm_rel s t po pi len
                (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) len) dat
                Hst Hrb Hw Hlen) as [Hst2 _].
    { rewrite Hzo, Hdat, <- app_assoc. reflexivity. }
    cbv zeta in Hst2. fold dat in Hst2.
    unfold dst_rel. split; [exact Hg|]. split; [exact Hl|]. split; [exact Hbw|].
    split; [exact Hsy|]. split; [exact Htr|].
    cbn [RD.zs_out RD.setZ_totalin RD.setZ_adler RD.setZ_done RD.setZ_in].
    exact Hst2.
Qed.

(** Group D's emission fields are untouched (the stream's output side is). *)
Lemma m_rb_em_view_window : forall s off size,
  DEmitDefs.em_view (fst (SLz.read_buf s (SLz.RB_window off) size)) = DEmitDefs.em_view s.
Proof.
  intros s off size.
  destruct (Z.eq_dec (Z.min size (DS.cs_avail_in (DS.ds_strm s))) 0) as [E|E].
  - rewrite m_s5_read_buf_zero by exact E. reflexivity.
  - rewrite m_s5_read_buf_window_eq by exact E. cbn [fst].
    destruct (m_s5_rb_strm_fields (DS.ds_strm s) (DS.ds_wrap s)
                (Z.min size (DS.cs_avail_in (DS.ds_strm s))) []) as (_ & _ & _ & _ & H5 & _ & H7 & H8 & _).
    unfold DEmitDefs.em_view. autorewrite with s5f_strm s5f_window. rewrite H5, H7, H8. reflexivity.
Qed.

Lemma m_rb_em_view_next_out : forall s size,
  DEmitDefs.em_view (fst (SLz.read_buf s SLz.RB_next_out size)) = DEmitDefs.em_view s.
Proof.
  intros s size.
  destruct (Z.eq_dec (Z.min size (DS.cs_avail_in (DS.ds_strm s))) 0) as [E|E].
  - rewrite m_s5_read_buf_zero by exact E. reflexivity.
  - rewrite m_s5_read_buf_next_out_eq by exact E. cbn [fst].
    destruct (m_s5_rb_strm_fields (DS.ds_strm s) (DS.ds_wrap s)
                (Z.min size (DS.cs_avail_in (DS.ds_strm s)))
                (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s))
                           (Z.min size (DS.cs_avail_in (DS.ds_strm s)))))
      as (_ & _ & _ & _ & H5 & _ & H7 & H8 & _).
    unfold DEmitDefs.em_view. autorewrite with s5f_strm. rewrite H5, H7, H8. reflexivity.
Qed.
