(** * Bridge.BrBits — pair 35 of PAIRS.md: the deflate bit writer, S5 vs RT.

    S5 keeps the C's layout: a bounded byte array [ds_pending_buf], an index
    [ds_pending_out] (head of the queue) and a COUNT [ds_pending], plus
    [ds_bi_buf]/[ds_bi_valid] inside the 66-field [deflate_state].  As in the
    C, the queue is [[pending_out, pending_out + pending)] ([flush_pending]
    copies [pending] bytes from [pending_out]) while [put_byte] writes at
    [pending_buf[pending]] — the tail only when [pending_out = 0], which zlib
    maintains whenever it appends (a partial flush returns to the caller, and
    the next call drains the queue, resetting [pending_out], before any byte
    is added).  RT keeps only what the C observes: the queue [bw_out] as a
    list, plus [bw_buf]/[bw_valid] ([ZBitsOut.BW]).

    Bridge style: a SIMULATION RELATION ([bw_rel]) — RT's queue is S5's slice
    [[pending_out, pending_out + pending)] — preserved by each operation,
    under a ROOM premise for appends: [pending_out = 0] (the append point is
    the tail) and [pending + k <= arr_len pending_buf] (k = bytes the
    operation may emit), because S5's array silently drops a write past its
    end while RT's list never fills.  Room is the obligation the callers
    discharge (zlib's own [pending_buf_size] accounting); it is the seam where
    the sym_buf overlay invariant will enter for [compress_block]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsOut.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelDefl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* 1.  Array-slice kit (S5's [parr] side)                                    *)
(* ------------------------------------------------------------------------- *)

Lemma slice_nat_snoc : forall {A} n (a : parr A) ofs,
  arr_slice_nat a ofs (S n) = arr_slice_nat a ofs n ++ [arr_get a (ofs + Z.of_nat n)].
Proof.
  induction n as [|n IH]; intros a ofs.
  - cbn [arr_slice_nat app]. rewrite Z.add_0_r. reflexivity.
  - change (arr_slice_nat a ofs (S (S n))) with (arr_get a ofs :: arr_slice_nat a (ofs + 1) (S n)).
    rewrite IH.
    replace (ofs + Z.of_nat (S n)) with (ofs + 1 + Z.of_nat n) by lia.
    reflexivity.
Qed.

Lemma slice_nat_set_out : forall {A} n (a : parr A) ofs j v,
  (j < ofs \/ ofs + Z.of_nat n <= j) ->
  arr_slice_nat (arr_set a j v) ofs n = arr_slice_nat a ofs n.
Proof.
  induction n as [|n IH]; intros a ofs j v Hj; [reflexivity|].
  cbn [arr_slice_nat]. rewrite arr_get_set_other by lia. rewrite IH by lia. reflexivity.
Qed.

(** Writing one byte at the tail of a queue that starts at 0 extends it by that byte. *)
Lemma slice_set_snoc0 : forall (a : arr) p v,
  0 <= p < arr_len a ->
  arr_slice (arr_set a p v) 0 (p + 1) = arr_slice a 0 p ++ [v].
Proof.
  intros a p v Hp. unfold arr_slice.
  replace (Z.to_nat (p + 1)) with (S (Z.to_nat p)) by lia.
  rewrite slice_nat_snoc.
  rewrite slice_nat_set_out by lia.
  replace (0 + Z.of_nat (Z.to_nat p)) with p by lia.
  rewrite arr_get_set_same by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The relation: [pend_rel], [bw_rel], [room], [flush_room] live in the  *)
(*     interface file [IRelDefl] (moved there unchanged)                     *)
(* ------------------------------------------------------------------------- *)

Lemma wrap8_u8 : forall v, wrap8 v = Base.u8 v.
Proof. intros v. rewrite wrap8_mod. reflexivity. Qed.

Lemma wrap16_u16 : forall v, wrap16 v = Base.u16 v.
Proof. intros v. rewrite wrap16_mod. reflexivity. Qed.

Lemma u8_land255 : forall w, Base.u8 (Z.land w 255) = Base.u8 w.
Proof.
  intros w. rewrite <- !wrap8_u8. unfold wrap8.
  rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  Per-operation simulation lemmas                                       *)
(* ------------------------------------------------------------------------- *)

Lemma sim_put_byte : forall s out c,
  pend_rel s out -> room s 1 ->
  pend_rel (DeflateState.put_byte s c) (out ++ [Base.u8 c])
  /\ DeflateState.ds_bi_buf (DeflateState.put_byte s c) = DeflateState.ds_bi_buf s
  /\ DeflateState.ds_bi_valid (DeflateState.put_byte s c) = DeflateState.ds_bi_valid s
  /\ DeflateState.ds_pending_out (DeflateState.put_byte s c) = DeflateState.ds_pending_out s
  /\ arr_len (DeflateState.ds_pending_buf (DeflateState.put_byte s c)) = arr_len (DeflateState.ds_pending_buf s)
  /\ DeflateState.ds_pending (DeflateState.put_byte s c) = DeflateState.ds_pending s + 1
  /\ DeflateState.ds_strm (DeflateState.put_byte s c) = DeflateState.ds_strm s.
Proof.
  intros s out c (Hpo & Hp & Hin & Hsl) [Hz Hroom]. unfold pend_rel.
  unfold DeflateState.put_byte, DeflateState.set_pending, DeflateState.set_pending_buf.
  cbn [DeflateState.ds_pending DeflateState.ds_pending_out DeflateState.ds_pending_buf
       DeflateState.ds_bi_buf DeflateState.ds_bi_valid DeflateState.ds_strm].
  rewrite arr_len_set.
  split; [|repeat split; reflexivity].
  rewrite Hz in *. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite slice_set_snoc0 by lia. rewrite Hsl, wrap8_u8. reflexivity.
Qed.

Lemma sim_put_short : forall s out w,
  pend_rel s out -> room s 2 ->
  pend_rel (Trees.put_short s w) (out ++ [Base.u8 w; Base.u8 (Z.shiftr (Base.u16 w) 8)])
  /\ DeflateState.ds_bi_buf (Trees.put_short s w) = DeflateState.ds_bi_buf s
  /\ DeflateState.ds_bi_valid (Trees.put_short s w) = DeflateState.ds_bi_valid s
  /\ DeflateState.ds_pending_out (Trees.put_short s w) = DeflateState.ds_pending_out s
  /\ arr_len (DeflateState.ds_pending_buf (Trees.put_short s w)) = arr_len (DeflateState.ds_pending_buf s)
  /\ DeflateState.ds_strm (Trees.put_short s w) = DeflateState.ds_strm s.
Proof.
  intros s out w Hp [Hz Hroom]. unfold Trees.put_short. cbv zeta.
  destruct (sim_put_byte s out (Z.land w 255) Hp ltac:(split; [exact Hz | lia]))
    as (Hp1 & Hb1 & Hv1 & Ho1 & Hl1 & Hn1 & Hs1).
  destruct (sim_put_byte _ _ (Z.shiftr (wrap16 w) 8) Hp1 ltac:(split; [congruence | lia]))
    as ((Hr2a & Hr2b & Hr2c & Hs2) & Hb2 & Hv2 & Ho2 & Hl2 & _ & Hst2).
  split; [| repeat split; congruence].
  split; [exact Hr2a|]. split; [exact Hr2b|]. split; [exact Hr2c|].
  rewrite Hs2, u8_land255, wrap16_u16, <- app_assoc. reflexivity.
Qed.

Theorem br_put_byte : forall s b c,
  bw_rel s b -> room s 1 -> bw_rel (DeflateState.put_byte s c) (ZBitsOut.bw_put_byte c b).
Proof.
  intros s b c (Hp & Hb & Hv) Hroom.
  destruct (sim_put_byte s _ c Hp Hroom) as (Hp1 & Hb1 & Hv1 & _).
  unfold bw_rel. cbn [ZBitsOut.bw_put_byte ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
  split; [exact Hp1|]. split; congruence.
Qed.

Theorem br_put_short : forall s b w,
  bw_rel s b -> room s 2 -> bw_rel (Trees.put_short s w) (ZBitsOut.bw_put_short w b).
Proof.
  intros s b w (Hp & Hb & Hv) Hroom.
  destruct (sim_put_short s _ w Hp Hroom) as (Hp1 & Hb1 & Hv1 & _).
  unfold bw_rel. rewrite ZBitsOut.bw_put_short_out.
  split; [exact Hp1|].
  cbn [ZBitsOut.bw_put_short ZBitsOut.bw_put_byte ZBitsOut.bw_buf ZBitsOut.bw_valid]. split; congruence.
Qed.

Theorem br_send_bits : forall s b value len,
  bw_rel s b -> room s 2 ->
  bw_rel (Trees.send_bits s value len) (ZBitsOut.bw_send_bits value len b).
Proof.
  intros s b value len (Hp & Hb & Hv) Hroom.
  unfold Trees.send_bits, ZBitsOut.bw_send_bits. cbv zeta.
  change DeflateState.Buf_size with 16. change ZBitsOut.Buf_size with 16.
  rewrite <- Hv, <- Hb, !wrap16_u16.
  set (m := Base.u16 (Z.lor (DeflateState.ds_bi_buf s)
                            (Z.shiftl (Base.u16 value) (DeflateState.ds_bi_valid s)))).
  destruct (Z.ltb (16 - len) (DeflateState.ds_bi_valid s)).
  - assert (Hp1 : pend_rel (DeflateState.set_bi_buf s m) (ZBitsOut.bw_out b)) by exact Hp.
    assert (Hr1 : room (DeflateState.set_bi_buf s m) 2) by exact Hroom.
    change (DeflateState.ds_bi_buf (DeflateState.set_bi_buf s m)) with m.
    destruct (sim_put_short _ _ m Hp1 Hr1) as (Hp2 & _ & Hv2 & _).
    change (DeflateState.ds_bi_valid (DeflateState.set_bi_buf s m))
      with (DeflateState.ds_bi_valid s) in Hv2.
    revert Hp2 Hv2. generalize (Trees.put_short (DeflateState.set_bi_buf s m) m). intros s2 Hp2 Hv2.
    unfold bw_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
    rewrite ZBitsOut.bw_put_short_out.
    unfold DeflateState.set_bi_valid, DeflateState.set_bi_buf, pend_rel.
    cbn [DeflateState.ds_bi_buf DeflateState.ds_bi_valid DeflateState.ds_pending_buf
         DeflateState.ds_pending_out DeflateState.ds_pending].
    rewrite Hv2.
    split; [exact Hp2|]. split; reflexivity.
  - unfold bw_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
    split; [exact Hp|]. split; reflexivity.
Qed.


Theorem br_bi_flush : forall s b,
  bw_rel s b -> flush_room s ->
  bw_rel (Trees.bi_flush s) (ZBitsOut.bw_flush b)
  /\ DeflateState.ds_pending_out (Trees.bi_flush s) = DeflateState.ds_pending_out s
  /\ arr_len (DeflateState.ds_pending_buf (Trees.bi_flush s)) = arr_len (DeflateState.ds_pending_buf s)
  /\ DeflateState.ds_strm (Trees.bi_flush s) = DeflateState.ds_strm s.
Proof.
  intros s b (Hp & Hb & Hv) Hfr.
  unfold Trees.bi_flush, ZBitsOut.bw_flush. cbv zeta. rewrite <- Hv, <- Hb.
  destruct (Z.eqb_spec (DeflateState.ds_bi_valid s) 16) as [E16|N16].
  - destruct Hfr as [Hlt|Hroom]; [lia|].
    destruct (sim_put_short s _ (DeflateState.ds_bi_buf s) Hp Hroom) as (Hp2 & _ & _ & Ho2 & Hl2 & Hs2).
    unfold bw_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
    rewrite ZBitsOut.bw_put_short_out.
    unfold DeflateState.set_bi_valid, DeflateState.set_bi_buf.
    cbn [DeflateState.ds_pending_out DeflateState.ds_pending_buf DeflateState.ds_strm].
    split; [split; [exact Hp2 | split; reflexivity]|]. split; [exact Ho2|]. split; [exact Hl2 | exact Hs2].
  - destruct (Z.leb_spec 8 (DeflateState.ds_bi_valid s)) as [G8|L8].
    + destruct Hfr as [Hlt|Hroom]; [lia|].
      destruct (sim_put_byte s _ (DeflateState.ds_bi_buf s) Hp ltac:(destruct Hroom; split; [assumption | lia]))
        as (Hp2 & Hb2 & Hv2 & Ho2 & Hl2 & _ & Hs2).
      unfold bw_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid ZBitsOut.bw_put_byte].
      unfold DeflateState.set_bi_valid, DeflateState.set_bi_buf, pend_rel.
      cbn [DeflateState.ds_bi_buf DeflateState.ds_bi_valid DeflateState.ds_pending_buf
           DeflateState.ds_pending_out DeflateState.ds_pending DeflateState.ds_strm].
      rewrite Hb2, Hv2.
      split; [split; [exact Hp2 | split; reflexivity]|]. split; [exact Ho2|]. split; [exact Hl2 | exact Hs2].
    + split; [exact (conj Hp (conj Hb Hv))|]. repeat split.
Qed.

Theorem br_bi_windup : forall s b,
  bw_rel s b -> room s 2 -> bw_rel (Trees.bi_windup s) (ZBitsOut.bw_windup b).
Proof.
  intros s b (Hp & Hb & Hv) Hroom.
  unfold Trees.bi_windup, ZBitsOut.bw_windup. cbv zeta. rewrite <- Hv, <- Hb.
  unfold bw_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
  destruct (Z.ltb 8 (DeflateState.ds_bi_valid s)).
  - destruct (sim_put_short s _ (DeflateState.ds_bi_buf s) Hp Hroom) as (Hp2 & _).
    rewrite ZBitsOut.bw_put_short_out. split; [exact Hp2|]. split; reflexivity.
  - destruct (Z.ltb 0 (DeflateState.ds_bi_valid s)).
    + destruct (sim_put_byte s _ (DeflateState.ds_bi_buf s) Hp ltac:(destruct Hroom; split; [assumption | lia]))
        as (Hp2 & _).
      cbn [ZBitsOut.bw_put_byte ZBitsOut.bw_out]. split; [exact Hp2|]. split; reflexivity.
    + split; [exact Hp|]. split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  Non-vacuity probes                                                    *)
(* ------------------------------------------------------------------------- *)

(** An S5 state built the way [deflateInit2_m] builds it ([ds_of_oracle] with
    the all-zero oracle the harness passes, then a 64 KiB pending buffer)
    against RT's [bw_init]: the same eight [send_bits] calls and a [windup]
    leave the same non-empty queue. *)
Definition s5_bw0 : DeflateState.deflate_state :=
  DeflateState.set_pending_buf
    (DeflateState.ds_of_oracle (fun _ => 0) 0%N
       (DeflateState.cstrm_of_call (mkZCall [] 0 zstrm0)))
    (arr_make 65536 0).

Definition calls : list (Z * Z) := [(5, 3); (300, 9); (1, 1); (65535, 16); (7, 3); (12, 5); (0, 7); (255, 8)].

Definition s5_run : DeflateState.deflate_state :=
  Trees.bi_windup (fold_left (fun s vl => Trees.send_bits s (fst vl) (snd vl)) calls s5_bw0).
Definition rt_run : ZBitsOut.BW :=
  ZBitsOut.bw_windup (fold_left (fun b vl => ZBitsOut.bw_send_bits (fst vl) (snd vl) b) calls ZBitsOut.bw_init).

Example probe_same_queue :
  arr_slice (DeflateState.ds_pending_buf s5_run) (DeflateState.ds_pending_out s5_run)
            (DeflateState.ds_pending s5_run)
  = ZBitsOut.bw_out rt_run
  /\ ZBitsOut.bw_out rt_run <> [].
Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

(** Both halves of [room] are real premises.  (a) With a 1-byte pending
    buffer S5 drops the second byte of a [put_short] that RT keeps.  (b) With
    a queue that does not start at 0 (one byte at index 1, [pending_out = 1],
    [pending = 1]) S5's [put_byte] writes at index [pending] = 1, OVER the
    queued byte, so its queue no longer extends RT's. *)
Example probe_room_needed :
  let s := DeflateState.set_pending_buf s5_bw0 (arr_make 1 0) in
  arr_slice (DeflateState.ds_pending_buf (Trees.put_short s 513)) 0
            (DeflateState.ds_pending (Trees.put_short s 513))
  <> ZBitsOut.bw_out (ZBitsOut.bw_put_short 513 ZBitsOut.bw_init).
Proof. cbv zeta. vm_compute. discriminate. Qed.

Example probe_tail_needed :
  let s := DeflateState.set_pending (DeflateState.set_pending_out
             (DeflateState.set_pending_buf s5_bw0 (arr_set (arr_make 65536 0) 1 7)) 1) 1 in
  pend_rel s [7]
  /\ arr_slice (DeflateState.ds_pending_buf (DeflateState.put_byte s 9))
               (DeflateState.ds_pending_out (DeflateState.put_byte s 9))
               (DeflateState.ds_pending (DeflateState.put_byte s 9))
     <> [7; 9].
Proof.
  cbv zeta. split.
  - unfold pend_rel. vm_compute. repeat split; try discriminate; reflexivity.
  - vm_compute. discriminate.
Qed.

Print Assumptions br_put_byte.
Print Assumptions br_put_short.
Print Assumptions br_send_bits.
Print Assumptions br_bi_flush.
Print Assumptions br_bi_windup.
