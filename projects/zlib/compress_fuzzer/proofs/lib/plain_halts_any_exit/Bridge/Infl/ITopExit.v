(** * Bridge.Infl.ITopExit — the end of the harness's inflate call ([inf_leave]), both models.

    Part of ITop.  When the loop has
    left in a state related by [IInv.ifin] with [Z_STREAM_END], each model's [inf_leave]
    ([inflate.c:1243-1273]) returns [Z_STREAM_END] and the bytes [[0, put)] of its output
    buffer: [ifin] has [out = left] (CHECK restarted the snapshot) and an unallocated window
    ([wsize = 0]), so [updatewindow] is not called, nothing is added to the totals or the check
    value, and [ret] is not rewritten to [Z_BUF_ERROR]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SI := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Inflate.

Lemma wrap64_small : forall x, 0 <= x < 2 ^ 64 -> wrap64 x = x.
Proof.
  intros x Hx. unfold wrap64. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx.
Qed.

(* ------------------------------------------------------------------------- *)
(* S5                                                                        *)
(* ------------------------------------------------------------------------- *)

Theorem s5_leave : forall (St : Type) (hooks : zhooks St) w q (chs : St),
  ifin w q -> RI.q_ret q = RBa.Z_STREAM_END ->
  exists s' zr, SI.inf_leave hooks Z_NO_FLUSH w chs = MRet ((s', zr), chs)
    /\ zr_output zr = arr_slice (IS.ic_outbuf (IS.w_c w)) 0 (IS.ir_put (IS.w_r w))
    /\ zr_rc zr = Z_STREAM_END
    /\ zs_total_out (zr_strm zr) = IS.ir_put (IS.w_r w).
Proof.
  intros St hooks w q chs [Hrel [Hout [Htot [Hws Hpl]]]] Hret.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp0 & Hl0 & _ & _ & _ & _ & _ & Hr).
  assert (Hr' : IS.ir_ret (IS.w_r w) = Z_STREAM_END) by (rewrite Hr, Hret; reflexivity).
  destruct w as [s c r]. cbn [IS.w_s IS.w_c IS.w_r] in *.
  unfold SI.inf_leave, IS.RESTORE. cbv beta zeta. cbn [IS.w_s IS.w_c IS.w_r].
  autorewrite with s5ic_avail_in s5ic_next_in s5ic_avail_out s5ic_next_out s5i_bits s5i_hold.
  rewrite Hout, Z.sub_diag. change (wrap32 0) with 0.
  change (negb (0 =? 0)) with false. rewrite andb_false_r. cbv beta iota zeta.
  autorewrite with s5ic_data_type s5ic_total_out s5ic_total_in s5i_total s5i_bits s5i_hold.
  rewrite Hws. change (negb (0 =? 0)) with false. cbn [andb orb sbind sret mbind fst snd].
  rewrite Hr'. change (Z_STREAM_END =? Z_OK) with false. rewrite andb_false_r.
  eexists _, _. split; [reflexivity|].
  unfold IS.zret_of_icall, IS.zstrm_of_icall. cbn [zr_output zr_rc zr_strm zs_total_out].
  autorewrite with s5ic_data_type s5ic_total_out s5ic_total_in s5ic_avail_in s5ic_next_in
    s5ic_avail_out s5ic_next_out.
  split; [reflexivity|]. split; [reflexivity|].
  rewrite Htot, Z.add_0_r. apply wrap64_small. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* RT                                                                        *)
(* ------------------------------------------------------------------------- *)

Theorem rt_leave : forall c w q,
  ifin w q -> RI.q_ret q = RBa.Z_STREAM_END ->
  RI.q_ob (fst (RI.inf_leave c q)) = RI.q_ob q /\ snd (RI.inf_leave c q) = RBa.Z_STREAM_END.
Proof.
  intros c w q [Hrel [Hout [_ [Hws _]]]] Hret.
  destruct Hrel as ((_ & Hw & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & _ & _ & _ & _ & _ & _ & Ho & _).
  destruct Hw as (_ & Hwsz & _).
  assert (Hq : RI.q_out q = RI.o_left (RI.q_ob q)) by congruence.
  assert (Hw0 : RI.w_wsize (RI.s_win (RI.q_st q)) = 0) by congruence.
  unfold RI.inf_leave, RI.q_restore. cbv beta zeta.
  cbn [RI.qset_st RI.q_st RI.q_ob RI.q_out RI.q_ret RI.set_bits RI.set_hold RI.s_win].
  rewrite Hw0, Hq, !Z.eqb_refl. cbn [negb andb orb].
  unfold RI.inf_leave_tail. cbv beta zeta.
  destruct (negb _ && negb _);
    cbn [RI.q_ob RI.q_ret RI.q_st RI.q_z RI.qset_ret RI.qset_z RI.qset_out RI.qset_in RI.qset_st
         RI.qcheck fst snd];
    rewrite Hret; change (RBa.Z_STREAM_END =? RBa.Z_OK) with false; rewrite andb_false_r;
    (split; reflexivity).
Qed.

(** The tail of [inf_leave] keeps [ret] unless it is [Z_OK]. *)
Lemma rt_tail_ret : forall c q1 wrote,
  snd (RI.inf_leave_tail c q1 wrote) = RBa.Z_STREAM_END -> RI.q_ret q1 = RBa.Z_STREAM_END.
Proof.
  intros c q1 wrote H. unfold RI.inf_leave_tail in H. cbv beta zeta in H.
  destruct (negb _ && negb _);
    cbn [RI.q_ob RI.q_ret RI.q_st RI.q_z RI.qset_ret RI.qset_z RI.qset_out RI.qset_in RI.qset_st
         RI.qcheck fst snd] in H;
    (destruct (_ && (RI.q_ret q1 =? RBa.Z_OK)); [vm_compute in H; discriminate H | exact H]).
Qed.

(** The converse the top needs: RT's call returns [Z_STREAM_END] only from a loop exit that
    carried it ([inf_leave] rewrites only [Z_OK], and its allocation failure is [Z_MEM_ERROR]). *)
Theorem rt_leave_ret : forall c q,
  snd (RI.inf_leave c q) = RBa.Z_STREAM_END -> RI.q_ret q = RBa.Z_STREAM_END.
Proof.
  intros c q H. unfold RI.inf_leave in H. cbv beta zeta in H.
  destruct (_ || _).
  - destruct (RI.uw _ _ _ _ _).
    + apply rt_tail_ret in H. unfold RI.q_restore in H. cbn [RI.qset_st RI.q_ret] in H. exact H.
    + vm_compute in H. discriminate H.
  - apply rt_tail_ret in H. unfold RI.q_restore in H. cbn [RI.qset_st RI.q_ret] in H. exact H.
Qed.
