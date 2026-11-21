(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate Uncompr InflateGarbBase InflateGarb ModelRel
  InflateInv InflateInvKit InflateInvLoop InflateInvApi InflateInvCall.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateIeq InflateIeqKit InflateIeqLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Ltac seq_unpack H :=
  unfold SEQ, SEQX, icoreq in H; proj_cbn_in H;
  destruct H as (?CORE & ?CK & ?LEN & ?OFS & ?EXT & ?LB & ?DB & ?DYN & ?ALl & ?ALw & ?ALc & ?ALn & ?LL & ?CL & ?CO & ?WIq & ?WW);
  injection CORE; clear CORE.
Ltac seq_goal :=
  unfold SEQ, SEQX, icoreq;
  cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk];
  split; [reflexivity|]; repeat match goal with |- _ /\ _ => split end.





Definition zret_dteq (r1 r2 : ZRet) : Prop :=
  zr_rc r2 = zr_rc r1 /\ zr_consumed r2 = zr_consumed r1 /\ zr_output r2 = zr_output r1
  /\ zs_total_in (zr_strm r2) = zs_total_in (zr_strm r1) /\ zs_total_out (zr_strm r2) = zs_total_out (zr_strm r1)
  /\ zs_adler (zr_strm r2) = zs_adler (zr_strm r1) /\ zs_msg (zr_strm r2) = zs_msg (zr_strm r1).
Definition zs_with_dt (z : zstrm) (dt : Z) : zstrm := mkZS (zs_total_in z) (zs_total_out z) (zs_adler z) dt (zs_msg z).


Lemma shl32_wbits : forall w, 8 <= w <= 15 -> shl32 1 w = 2 ^ w.
Proof.
  intros w Hw. unfold shl32. rewrite Z.shiftl_1_l. apply wrap32_id.
  split; [apply Z.pow_nonneg; lia|]. apply Z.pow_lt_mono_r; lia.
Qed.


#[local] Transparent UPDATE_CHECK_bytes.

Section UW.
  Context {St : Type}.
  Variable hooks : zhooks St.



  Ltac uwred := cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk
       iset_wsize iset_whave iset_wnext iset_window].
  Ltac uw_len ALn := rewrite !arr_len_blit; exact ALn.
  Ltac uw_wdw := unfold WDW; cbn [is_wbits is_sane is_whave is_wsize is_wnext is_window_blk is_window]; rewrite !arr_len_blit;
                 repeat match goal with |- _ /\ _ => split end; first [assumption | lia | (right; assumption) | idtac].




End UW.



Section Leave.
  Context {St : Type}.
  Variable hooks : zhooks St.
  Variable flush : Z.

  Ltac lvred := cbn [RESTORE w_s w_c w_r cdt
       icset_next_out icset_avail_out icset_next_in icset_avail_in icset_total_in icset_total_out icset_adler icset_data_type
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg
       iset_hold iset_bits iset_total iset_check iset_mode
       is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
  Ltac zret_tac := unfold zret_dteq, zret_of_icall, zstrm_of_icall;
                   cbn [zr_rc zr_consumed zr_output zr_strm zs_total_in zs_total_out zs_adler zs_msg
                        ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg];
                   repeat split; reflexivity.

End Leave.





Section Inflate.
  Variable iv : ivariant.
  Context {St : Type}.
  Variable hooks : zhooks St.


End Inflate.



Section U2Tail.
  Local Open Scope sm_scope.
  Context {St : Type}.
  Variable hooks : zhooks St.

End U2Tail.

Definition u2_with_sd (x : u2st) (s : inflate_state) (dt : Z) : u2st :=
  mkU2 s (zs_with_dt (u2_z x) dt) (u2_len x) (u2_left x) (u2_in_pos x) (u2_avail_in x) (u2_avail_out x) (u2_out_rev x) (u2_err x).

Section U2.
  Hypothesis LEAVE : leave_ui_stmt.
  Context {St : Type}.
  Variable hooks : zhooks St.


  Ltac x_open EX :=
    unfold u2_with_sd, zs_with_dt in EX; cbn in EX; injection EX; intros; subst.




End U2.
