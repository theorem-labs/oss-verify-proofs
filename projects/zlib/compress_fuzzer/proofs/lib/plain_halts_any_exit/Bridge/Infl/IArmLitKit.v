(** * Bridge.Infl.IArmLitKit — the kit of pair I10 (helper pci-len): moving [icore] and the
    two decoding tables across the state writes the decode arms make.

    Every lemma here takes [icore w q] (or [icb w q] = [icore] + [tviews_blk]) to the same
    invariant after one write on both sides: a reader move ([wbr] / [qset_br]), one
    [ICur] field or the mode ([iset_*] / [set_*]), or the output buffer and the
    [put]/[left] registers ([T_outp], stated over projections so that it applies to any
    term shape the arms build).  The decode arms chain these lemmas forward along S5's
    statement sequence; RT's own state is then convertible to the end of the chain. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* Arithmetic                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma k_wrap8_u8 : forall z, wrap8 z = RBa.u8 z.
Proof. intros z. rewrite wrap8_mod. reflexivity. Qed.

Lemma k_wrap32_u32 : forall z, wrap32 z = RBa.u32 z.
Proof. intros z. rewrite wrap32_mod. reflexivity. Qed.

Lemma k_swrap32_add : forall u v, swrap32 (swrap32 u + v) = swrap32 (u + v).
Proof.
  intros u v. unfold swrap32, two31. rewrite !wrap32_mod. f_equal.
  replace ((u + 2147483648) mod 2 ^ 32 - 2147483648 + v + 2147483648)
    with ((u + 2147483648) mod 2 ^ 32 + v) by ring.
  rewrite Z.add_mod_idemp_l by lia. f_equal. ring.
Qed.

Lemma k_swrap32_0 : swrap32 0 = 0.
Proof. reflexivity. Qed.

Lemma k_swrap32_m1 : swrap32 (-1) = -1.
Proof. reflexivity. Qed.

Lemma k_zok_ne_end : RBa.Z_OK <> RBa.Z_STREAM_END.
Proof. unfold RBa.Z_OK, RBa.Z_STREAM_END. discriminate. Qed.

(* ------------------------------------------------------------------------- *)
(* Tactics                                                                   *)
(* ------------------------------------------------------------------------- *)

Ltac icore_unf :=
  unfold icore, iw_rel, ist_core_rel, hdr_rel, win_rel, cur_rel, tab_rel, bld_rel, zstrm_rel.

Ltac destr_all := repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac split_all := repeat match goal with |- _ /\ _ => split end.

Ltac rt_cbn :=
  cbn [RI.qset_st RI.qset_br RI.qset_ob RI.qset_z RI.qset_in RI.qset_out RI.qset_ret RI.qmode
       RI.set_mode RI.set_length RI.set_offset RI.set_extra RI.set_back RI.set_was
       RI.q_st RI.q_br RI.q_ob RI.q_z RI.q_in RI.q_out RI.q_ret RI.q_mode
       RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld RI.s_hold RI.s_bits
       RI.h_mode RI.h_last RI.h_wrap RI.h_havedict RI.h_flags RI.h_dmax RI.h_check RI.h_total RI.h_head
       RI.w_wbits RI.w_wsize RI.w_whave RI.w_wnext RI.w_alloc RI.w_win
       RI.u_length RI.u_offset RI.u_extra RI.u_back RI.u_was
       RI.t_lencode RI.t_distcode RI.t_lenbits RI.t_distbits RI.t_next RI.t_codes RI.t_sane
       RI.b_ncode RI.b_nlen RI.b_ndist RI.b_have RI.b_lens RI.b_work
       RI.o_buf RI.o_put RI.o_left RI.z_tin RI.z_tout RI.z_adler RI.z_dtype RI.z_msg].

(* ------------------------------------------------------------------------- *)
(* Facts read off [icore]                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma icore_mode : forall w q, icore w q -> IS.is_mode (IS.w_s w) = RI.m_val (RI.q_mode q).
Proof. intros w q H. exact (proj1 (proj1 (proj1 (proj1 H)))). Qed.

Lemma icore_cur : forall w q, icore w q -> cur_rel (IS.w_s w) (RI.s_cur (RI.q_st q)).
Proof. intros w q H. exact (proj1 (proj2 (proj2 (proj1 (proj1 H))))). Qed.

Lemma icore_ret : forall w q, icore w q -> RI.q_ret q = RBa.Z_OK.
Proof. intros w q H. exact (proj1 (proj2 H)). Qed.

Lemma icore_regs : forall w q, icore w q ->
  IS.ir_put (IS.w_r w) = RI.o_put (RI.q_ob q) /\ IS.ir_left (IS.w_r w) = RI.o_left (RI.q_ob q)
  /\ IS.ir_have (IS.w_r w) = RB.br_have (RI.q_br q) /\ IS.ir_out (IS.w_r w) = RI.q_out q
  /\ 0 <= IS.ir_put (IS.w_r w) /\ 0 <= IS.ir_left (IS.w_r w)
  /\ IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w) < 2 ^ 31
  /\ IS.ir_out (IS.w_r w) = IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w).
Proof.
  intros w q H. revert H. icore_unf. cbv zeta. intros H. destr_all.
  split_all; assumption.
Qed.

Lemma icore_win : forall w q, icore w q ->
  IS.is_whave (IS.w_s w) = 0 /\ RI.w_whave (RI.s_win (RI.q_st q)) = 0
  /\ IS.is_sane (IS.w_s w) = 1 /\ RI.t_sane (RI.s_tab (RI.q_st q)) = 1.
Proof.
  intros w q H. revert H. icore_unf. cbv zeta. intros H. destr_all.
  split_all; congruence.
Qed.

(** The whole output buffer, written prefix and zeroed tail, agrees. *)
Lemma icore_outbuf : forall w q, icore w q ->
  arr_len (IS.ic_outbuf (IS.w_c w)) = IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w)
  /\ arr_rel (IS.ic_outbuf (IS.w_c w)) (RI.o_buf (RI.q_ob q)) 0
             (IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w)).
Proof.
  intros w q H. revert H. icore_unf. cbv zeta. intros H. destr_all.
  split; [assumption|].
  intros i Hi. destruct (Z.lt_ge_cases i (IS.ir_put (IS.w_r w))) as [L|L].
  - match goal with Hr : arr_rel _ _ 0 (IS.ir_put _) |- _ => apply Hr; lia end.
  - match goal with Hr : arr_rel _ _ (IS.ir_put _) _ |- _ => apply Hr; lia end.
Qed.

Lemma mval_ne_head : forall m, m <> RI.M_HEAD -> RI.m_val m <> IS.HEAD.
Proof.
  intros m Hm. unfold IS.HEAD.
  destruct m; cbn [RI.m_val]; first [discriminate | exfalso; apply Hm; reflexivity].
Qed.

Lemma icore_not_head : forall w q, icore w q -> RI.q_mode q <> RI.M_HEAD ->
  IS.is_mode (IS.w_s w) <> IS.HEAD.
Proof. intros w q H Hm. rewrite (icore_mode w q H). apply mval_ne_head. exact Hm. Qed.

Lemma icore_obytes : forall w q, icore w q -> zbytes (RI.o_buf (RI.q_ob q)).
Proof.
  intros w q H. unfold icore in H. cbv zeta in H.
  repeat match type of H with _ /\ (_ /\ _) => apply proj2 in H end. exact (proj2 H).
Qed.

Lemma icore_wbytes : forall w q, icore w q -> zbytes (RI.w_win (RI.s_win (RI.q_st q))).
Proof.
  intros w q H. unfold icore in H. cbv zeta in H.
  repeat match type of H with _ /\ (_ /\ _) => apply proj2 in H end. exact (proj1 H).
Qed.

Lemma u8_byte : forall v, 0 <= RBa.u8 v < 256.
Proof. intros v. unfold RBa.u8. apply Z.mod_pos_bound. lia. Qed.

(* ------------------------------------------------------------------------- *)
(* Leaves and BAD targets                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma step_ok_leave_ok : forall sr q', RI.q_ret q' = RBa.Z_OK -> step_ok sr (RI.InfLeave q').
Proof.
  intros sr q' H. unfold step_ok. intros H'. exfalso. apply k_zok_ne_end. congruence.
Qed.

Lemma step_ok_bad : forall sr q', RI.q_mode q' = RI.M_BAD -> step_ok sr (RI.InfCont q').
Proof. intros sr q' H. unfold step_ok. intros H'. contradiction. Qed.

Lemma step_ok_cont : forall w' q', inv w' q' -> step_ok (IS.ARun tt w') (RI.InfCont q').
Proof. intros w' q' H. unfold step_ok. intros _. exists w'. split; [reflexivity|exact H]. Qed.

Lemma qbad_mode : forall q m, RI.q_mode (RI.qbad q m) = RI.M_BAD.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* The tables                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma code_at_codes : forall s s' p, IS.is_codes s' = IS.is_codes s -> IS.code_at s' p = IS.code_at s p.
Proof. intros s s' p H. unfold IS.code_at. rewrite H. reflexivity. Qed.

Lemma tbl_of_tab : forall st st' r, RI.s_tab st' = RI.s_tab st -> RI.tbl_of st' r = RI.tbl_of st r.
Proof. intros st st' r H. unfold RI.tbl_of. rewrite H. reflexivity. Qed.

Lemma tvb_tr : forall w q w' q', tviews_blk w q ->
  IS.is_codes (IS.w_s w') = IS.is_codes (IS.w_s w) ->
  IS.is_lencode (IS.w_s w') = IS.is_lencode (IS.w_s w) ->
  IS.is_distcode (IS.w_s w') = IS.is_distcode (IS.w_s w) ->
  IS.is_lenbits (IS.w_s w') = IS.is_lenbits (IS.w_s w) ->
  IS.is_distbits (IS.w_s w') = IS.is_distbits (IS.w_s w) ->
  RI.s_tab (RI.q_st q') = RI.s_tab (RI.q_st q) ->
  tviews_blk w' q'.
Proof.
  intros w q w' q' H Hc Hl Hd Hlb Hdb Ht. unfold tviews_blk in *. cbv zeta in *.
  rewrite Hl, Hd, Hlb, Hdb, Ht.
  rewrite !(code_at_codes (IS.w_s w) (IS.w_s w') _ Hc).
  rewrite !(tbl_of_tab (RI.q_st q) (RI.q_st q') _ Ht).
  exact H.
Qed.

(** [icore] + the two tables: the invariant of the Huffman-block modes. *)
Definition icb (w : IS.iw) (q : RI.InfSt) : Prop := icore w q /\ tviews_blk w q.

Lemma icb_brel : forall w q, icb w q -> brel w (RI.q_br q).
Proof. intros w q [H _]. exact (icore_brel w q H). Qed.

(** [inv] at the target modes of the decode arms. *)
Lemma inv_blk : forall w q, icb w q ->
  RI.q_mode q = RI.M_LEN \/ RI.q_mode q = RI.M_LIT \/ RI.q_mode q = RI.M_LEN_ -> inv w q.
Proof.
  intros w q [H T] Hm. split; [exact H|]. unfold imode.
  destruct Hm as [E|[E|E]]; rewrite E; exact T.
Qed.

Lemma inv_type : forall w q, icore w q -> RI.q_mode q = RI.M_TYPE -> inv w q.
Proof. intros w q H Hm. split; [exact H|]. unfold imode. rewrite Hm. exact I. Qed.

Lemma inv_match : forall w q, icb w q -> RI.q_mode q = RI.M_MATCH ->
  0 <= RI.u_length (RI.s_cur (RI.q_st q)) <= 258 -> 1 <= RI.u_offset (RI.s_cur (RI.q_st q)) <= 32768 ->
  inv w q.
Proof.
  intros w q [H T] Hm HL HO. split; [exact H|]. unfold imode. rewrite Hm.
  pose proof (icore_cur w q H) as (EL & EO & _). rewrite EL, EO. tauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* One write, both sides                                                     *)
(* ------------------------------------------------------------------------- *)

Ltac tclose := split_all; first [assumption | reflexivity | (intros _; auto)].

Lemma T_mode : forall w q v m, icore w q -> IS.is_mode (IS.w_s w) <> IS.HEAD -> v = RI.m_val m ->
  icore (IS.wset_s w (IS.iset_mode (IS.w_s w) v)) (RI.qmode q m).
Proof.
  intros w q v m H Hm ->. revert H. unfold RI.qmode. icore_unf. cbv zeta.
  autorewrite with s5w s5i_mode. rt_cbn. intros H. destr_all. tclose.
Qed.

Lemma T_length : forall w q v v', icore w q -> v = v' ->
  icore (IS.wset_s w (IS.iset_length (IS.w_s w) v)) (RI.qset_st q (RI.set_length (RI.q_st q) v')).
Proof.
  intros w q v v' H <-. revert H. icore_unf. cbv zeta.
  autorewrite with s5w s5i_length. rt_cbn. intros H. destr_all. tclose.
Qed.

Lemma T_offset : forall w q v v', icore w q -> v = v' ->
  icore (IS.wset_s w (IS.iset_offset (IS.w_s w) v)) (RI.qset_st q (RI.set_offset (RI.q_st q) v')).
Proof.
  intros w q v v' H <-. revert H. icore_unf. cbv zeta.
  autorewrite with s5w s5i_offset. rt_cbn. intros H. destr_all. tclose.
Qed.

Lemma T_extra : forall w q v v', icore w q -> v = v' ->
  icore (IS.wset_s w (IS.iset_extra (IS.w_s w) v)) (RI.qset_st q (RI.set_extra (RI.q_st q) v')).
Proof.
  intros w q v v' H <-. revert H. icore_unf. cbv zeta.
  autorewrite with s5w s5i_extra. rt_cbn. intros H. destr_all. tclose.
Qed.

Lemma T_offext : forall w q v1 v1' v2 v2', icore w q -> v1 = v1' -> v2 = v2' ->
  icore (IS.wset_s w (IS.iset_extra (IS.iset_offset (IS.w_s w) v1) v2))
        (RI.qset_st q (RI.set_extra (RI.set_offset (RI.q_st q) v1') v2')).
Proof.
  intros w q v1 v1' v2 v2' H <- <-. revert H. icore_unf. cbv zeta.
  autorewrite with s5w s5i_extra s5i_offset. rt_cbn. intros H. destr_all. tclose.
Qed.

Lemma T_was : forall w q v v', icore w q -> v = v' ->
  icore (IS.wset_s w (IS.iset_was (IS.w_s w) v)) (RI.qset_st q (RI.set_was (RI.q_st q) v')).
Proof.
  intros w q v v' H <-. revert H. icore_unf. cbv zeta.
  autorewrite with s5w s5i_was. rt_cbn. intros H. destr_all. tclose.
Qed.

Lemma T_back : forall w q v v', icore w q -> v = swrap32 v' ->
  icore (IS.wset_s w (IS.iset_back (IS.w_s w) v)) (RI.qset_st q (RI.set_back (RI.q_st q) v')).
Proof.
  intros w q v v' H ->. revert H. icore_unf. cbv zeta.
  autorewrite with s5w s5i_back. rt_cbn. intros H. destr_all. tclose.
Qed.

Lemma T_addback : forall w q v, icore w q ->
  icore (IS.wset_s w (IS.iset_back (IS.w_s w) (swrap32 (IS.is_back (IS.w_s w) + v))))
        (RI.qset_st q (RI.set_back (RI.q_st q) (RI.u_back (RI.s_cur (RI.q_st q)) + v))).
Proof.
  intros w q v H. apply T_back; [exact H|].
  pose proof (icore_cur w q H) as (_ & _ & _ & Hb & _). rewrite Hb. apply k_swrap32_add.
Qed.

(** The reader moves.  [bnx] is [bits - 8 next]: it never grows (a pull adds 8 to both
    sides, a drop lowers [bits]), which keeps [bits <= 8 next]. *)
Definition bnx (b : RB.BR) : Z := RB.br_bits b - 8 * RB.br_next b.

Lemma T_br : forall w q b', icore w q -> brel (wbr w b') b' ->
  RB.br_in b' = RB.br_in (RI.q_br q) ->
  RB.br_next b' + RB.br_have b' = RB.br_next (RI.q_br q) + RB.br_have (RI.q_br q) ->
  bnx b' <= bnx (RI.q_br q) ->
  icore (wbr w b') (RI.qset_br q b').
Proof.
  intros w q b' H Hb Hin Hsum Hbnx. unfold bnx in Hbnx. unfold brel in Hb.
  revert H Hb. icore_unf. cbv zeta. rewrite !wbr_s, !wbr_c, !wbr_r. setbr_cbn. rt_cbn.
  intros H Hb. destr_all. rewrite Hin.
  split_all; first [assumption | reflexivity | lia].
Qed.

(** Output-buffer and register writes, over projections. *)
Lemma T_outp : forall w q w' q',
  icore w q ->
  IS.w_s w' = IS.w_s w ->
  RI.q_st q' = RI.q_st q -> RI.q_z q' = RI.q_z q -> RI.q_br q' = RI.q_br q ->
  RI.q_in q' = RI.q_in q -> RI.q_out q' = RI.q_out q -> RI.q_ret q' = RI.q_ret q ->
  IS.ic_input (IS.w_c w') = IS.ic_input (IS.w_c w) ->
  IS.ic_total_in (IS.w_c w') = IS.ic_total_in (IS.w_c w) ->
  IS.ic_total_out (IS.w_c w') = IS.ic_total_out (IS.w_c w) ->
  IS.ic_adler (IS.w_c w') = IS.ic_adler (IS.w_c w) ->
  IS.ic_data_type (IS.w_c w') = IS.ic_data_type (IS.w_c w) ->
  IS.ir_next (IS.w_r w') = IS.ir_next (IS.w_r w) ->
  IS.ir_have (IS.w_r w') = IS.ir_have (IS.w_r w) ->
  IS.ir_hold (IS.w_r w') = IS.ir_hold (IS.w_r w) ->
  IS.ir_bits (IS.w_r w') = IS.ir_bits (IS.w_r w) ->
  IS.ir_in (IS.w_r w') = IS.ir_in (IS.w_r w) ->
  IS.ir_out (IS.w_r w') = IS.ir_out (IS.w_r w) ->
  IS.ir_ret (IS.w_r w') = IS.ir_ret (IS.w_r w) ->
  arr_len (IS.ic_outbuf (IS.w_c w')) = arr_len (IS.ic_outbuf (IS.w_c w)) ->
  IS.ir_put (IS.w_r w') = RI.o_put (RI.q_ob q') -> IS.ir_left (IS.w_r w') = RI.o_left (RI.q_ob q') ->
  0 <= IS.ir_put (IS.w_r w') -> 0 <= IS.ir_left (IS.w_r w') ->
  IS.ir_put (IS.w_r w') + IS.ir_left (IS.w_r w') = IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w) ->
  arr_rel (IS.ic_outbuf (IS.w_c w')) (RI.o_buf (RI.q_ob q')) 0
          (IS.ir_put (IS.w_r w') + IS.ir_left (IS.w_r w')) ->
  zbytes (RI.o_buf (RI.q_ob q')) ->
  icore w' q'.
Proof.
  intros w q w' q' H Hs Hst Hz Hbr Hqin Hqout Hqret Hci Hcti Hcto Hca Hcd Hn Hv Hh Hb Hi Ho Hr
    Hlen Hput Hleft Hp0 Hl0 Hsum Hrel Hby. unfold zbytes in Hby.
  revert H. icore_unf. cbv zeta.
  rewrite Hs, Hst, Hz, Hbr, Hqin, Hqout, Hqret, Hci, Hcti, Hcto, Hca, Hcd, Hn, Hv, Hh, Hb, Hi, Ho, Hr.
  intros H. destr_all.
  split_all; first [assumption | lia | idtac].
  - refine (arr_rel_narrow _ _ _ _ _ _ _ _ Hrel); lia.
  - refine (arr_rel_narrow _ _ _ _ _ _ _ _ Hrel); lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* The same writes on [icb]                                                  *)
(* ------------------------------------------------------------------------- *)

Ltac tvb_go H :=
  apply (tvb_tr _ _ _ _ H);
  first [ autorewrite with s5w s5i_mode s5i_length s5i_offset s5i_extra s5i_back s5i_was;
          rewrite ?wbr_s; reflexivity
        | reflexivity ].

Lemma B_mode : forall w q v m, icb w q -> IS.is_mode (IS.w_s w) <> IS.HEAD -> v = RI.m_val m ->
  icb (IS.wset_s w (IS.iset_mode (IS.w_s w) v)) (RI.qmode q m).
Proof.
  intros w q v m [H T] Hm Hv. split; [apply T_mode; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_mode; reflexivity.
Qed.

Lemma B_length : forall w q v v', icb w q -> v = v' ->
  icb (IS.wset_s w (IS.iset_length (IS.w_s w) v)) (RI.qset_st q (RI.set_length (RI.q_st q) v')).
Proof.
  intros w q v v' [H T] Hv. split; [apply T_length; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_length; reflexivity.
Qed.

Lemma B_extra : forall w q v v', icb w q -> v = v' ->
  icb (IS.wset_s w (IS.iset_extra (IS.w_s w) v)) (RI.qset_st q (RI.set_extra (RI.q_st q) v')).
Proof.
  intros w q v v' [H T] Hv. split; [apply T_extra; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_extra; reflexivity.
Qed.

Lemma B_offset : forall w q v v', icb w q -> v = v' ->
  icb (IS.wset_s w (IS.iset_offset (IS.w_s w) v)) (RI.qset_st q (RI.set_offset (RI.q_st q) v')).
Proof.
  intros w q v v' [H T] Hv. split; [apply T_offset; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_offset; reflexivity.
Qed.

Lemma B_offext : forall w q v1 v1' v2 v2', icb w q -> v1 = v1' -> v2 = v2' ->
  icb (IS.wset_s w (IS.iset_extra (IS.iset_offset (IS.w_s w) v1) v2))
      (RI.qset_st q (RI.set_extra (RI.set_offset (RI.q_st q) v1') v2')).
Proof.
  intros w q v1 v1' v2 v2' [H T] H1 H2. split; [apply T_offext; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_extra s5i_offset; reflexivity.
Qed.

Lemma B_was : forall w q v v', icb w q -> v = v' ->
  icb (IS.wset_s w (IS.iset_was (IS.w_s w) v)) (RI.qset_st q (RI.set_was (RI.q_st q) v')).
Proof.
  intros w q v v' [H T] Hv. split; [apply T_was; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_was; reflexivity.
Qed.

Lemma B_back : forall w q v v', icb w q -> v = swrap32 v' ->
  icb (IS.wset_s w (IS.iset_back (IS.w_s w) v)) (RI.qset_st q (RI.set_back (RI.q_st q) v')).
Proof.
  intros w q v v' [H T] Hv. split; [apply T_back; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_back; reflexivity.
Qed.

Lemma B_addback : forall w q v, icb w q ->
  icb (IS.wset_s w (IS.iset_back (IS.w_s w) (swrap32 (IS.is_back (IS.w_s w) + v))))
      (RI.qset_st q (RI.set_back (RI.q_st q) (RI.u_back (RI.s_cur (RI.q_st q)) + v))).
Proof.
  intros w q v [H T]. split; [apply T_addback; assumption|].
  apply (tvb_tr _ _ _ _ T); autorewrite with s5w s5i_back; reflexivity.
Qed.

Lemma B_br : forall w q b', icb w q -> brel (wbr w b') b' ->
  RB.br_in b' = RB.br_in (RI.q_br q) ->
  RB.br_next b' + RB.br_have b' = RB.br_next (RI.q_br q) + RB.br_have (RI.q_br q) ->
  bnx b' <= bnx (RI.q_br q) ->
  icb (wbr w b') (RI.qset_br q b').
Proof.
  intros w q b' [H T] Hb Hin Hsum Hbnx. split; [apply T_br; assumption|].
  apply (tvb_tr _ _ _ _ T); rewrite ?wbr_s; reflexivity.
Qed.

(** [bnx] along RT's reader functions. *)
Lemma nb_go_bnx : forall f n b b', RI.inf_nb_go f n b = RI.NBOk b' ->
  bnx b' = bnx b /\ RB.br_in b' = RB.br_in b.
Proof.
  induction f as [|f IH]; intros n b b' H; cbn [RI.inf_nb_go] in H.
  - destruct (RB.br_bits b <? n); [discriminate|]. injection H as <-. split; reflexivity.
  - destruct (RB.br_bits b <? n).
    + destruct (RB.br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
      destruct (IH n b1 b' H) as [E1 E2].
      pose proof (RB.br_pullbyte_step b b1 Hp) as (_ & Hn & Hbt & Hi).
      unfold bnx in *. split; [lia|congruence].
    + injection H as <-. split; reflexivity.
Qed.

Lemma nb_bnx : forall n b b', RI.inf_nb n b = RI.NBOk b' -> bnx b' = bnx b /\ RB.br_in b' = RB.br_in b.
Proof. intros n b b'. unfold RI.inf_nb. apply nb_go_bnx. Qed.

Lemma gfetch_bnx : forall f ix t cb b h b', gfetch f ix t cb b = RI.FetchOk h b' ->
  bnx b' = bnx b /\ RB.br_in b' = RB.br_in b.
Proof.
  induction f as [|f IH]; intros ix t cb b h b' H; cbn [gfetch] in H; [discriminate|].
  destruct (Z.leb _ _).
  - injection H as _ <-. split; reflexivity.
  - destruct (RB.br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
    destruct (IH ix t cb b1 h b' H) as [E1 E2].
    pose proof (RB.br_pullbyte_step b b1 Hp) as (_ & Hn & Hbt & Hi).
    unfold bnx in *. split; [lia|congruence].
Qed.

Lemma fetch_bnx : forall t nb b h b', RI.inf_fetch t nb b = RI.FetchOk h b' ->
  bnx b' = bnx b /\ RB.br_in b' = RB.br_in b.
Proof. intros t nb b h b'. unfold RI.inf_fetch. rewrite fetch_gfetch. apply gfetch_bnx. Qed.

Lemma fetch2_bnx : forall t lst b h b', RI.inf_fetch2 t lst b = RI.FetchOk h b' ->
  bnx b' = bnx b /\ RB.br_in b' = RB.br_in b.
Proof. intros t lst b h b'. unfold RI.inf_fetch2. rewrite fetch2_gfetch. apply gfetch_bnx. Qed.

Lemma drop_bnx : forall n b, bnx (RB.br_dropbits n b) = bnx b - n.
Proof. intros n b. unfold bnx. cbn [RB.br_dropbits RB.br_bits RB.br_next]. lia. Qed.
